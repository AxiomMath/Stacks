module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation

/-!
# The étale neighbourhood an étale algebra over an affine chart determines

Let `X` be a scheme, let `x` be a point of `X`, let `U` be an affine open of `X` containing `x`
and let `r : Γ(X, U) → D` be a ring map whose spectrum is étale. A prime `u` of `D` contracting
to the prime of `x` makes

```
Spec D ⟶ Spec Γ(X, U) ≅ U ↪ X
```

an étale neighbourhood of `(X, x)` with distinguished point `u`. This file constructs that
neighbourhood and proves that its scheme is affine, that it is **elementary** as soon as `r`
induces a bijection of residue fields at `u`, and that its map of local rings carries the germ of
a section `a` of `U` to the image of `r a` in the localization of `D` at `u`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.etaleNeighborhoodOfChart`: the neighbourhood.
* `AlgebraicGeometry.IsAffineOpen.isElementary_etaleNeighborhoodOfChart`: it is elementary when
  the residue field does not grow.
* `AlgebraicGeometry.IsAffineOpen.stalkIso_stalkHom_etaleNeighborhoodOfChart_germ`: its map of
  local rings, read through the canonical identification of the local ring of `Spec D` at `u`
  with the localization of `D` there, carries the germ of `a : Γ(X, U)` to `r a`.
* `AlgebraicGeometry.IsAffineOpen.stalkHom_etaleNeighborhoodOfChart`: the same identity in the
  form of a square with `Localization.localRingHom`, given an identification of the local ring of
  `X` at `x` with a localization of `Γ(X, U)`.
* `AlgebraicGeometry.IsAffineOpen.apply_fromSpec_of_comap_eq`: where a morphism sends the point
  of an affine open that a prime of its section ring cuts out.
* `AlgebraicGeometry.IsAffineOpen.specMap_fromSpec_apply` and
  `AlgebraicGeometry.IsAffineOpen.specMap_fromSpec_comp`: for the morphism
  `Spec D ⟶ Spec Γ(T, W) ≅ W ↪ T` attached to a ring map `Γ(T, W) → D`, where a prime of `D`
  goes, and what its composite with a morphism `T ⟶ S` is.

## Implementation notes

The étaleness is the hypothesis `Etale (Spec.map (CommRingCat.ofHom r))` on the spectrum rather
than `Algebra.Etale`, so that it applies to ring maps that are not an `algebraMap`; the two are
related by `RingHom.etale_algebraMap` and `AlgebraicGeometry.HasRingHomProperty.Spec_iff`.

The map of local rings is described on germs, which mentions no identification of `𝒪_{X, x}`
with a localization; the square with `Localization.localRingHom`, stated against such an
identification, follows since two ring maps out of a localization that agree on the image of the
ring agree.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing StacksDraft.ArtinApproximation

universe u

namespace AlgebraicGeometry

attribute [local instance] PrimeSpectrum.isPrime

variable {X : Scheme.{u}} {U : X.Opens}

/-! ### A morphism out of `Spec D` attached to a ring map on an affine chart -/

/-- **Where the morphism `Spec D ⟶ Spec Γ(X, U) ≅ U ↪ X` sends a prime.** If the prime `u` of
`D` contracts along `r : Γ(X, U) → D` to the prime of the point `x` of the affine open `U`, then
the morphism `r` determines carries `u` to `x`. -/
theorem IsAffineOpen.specMap_fromSpec_apply (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)
    {D : Type u} [CommRing D] (r : Γ(X, U) →+* D) (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    (Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec) u = x := by
  change hU.fromSpec (Spec.map (CommRingCat.ofHom r) u) = x
  rw [show Spec.map (CommRingCat.ofHom r) u = hU.primeIdealOf ⟨x, hxU⟩ from
    PrimeSpectrum.ext hu]
  exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩

/-- **Where a morphism sends the point of an affine open cut out by a prime.** Let `k : X ⟶ Y`
carry an affine open `U_X` of `X` into an affine open `V_Y` of `Y`, let `q` be a prime of
`Γ(X, U_X)` and let `y` be a point of `V_Y`. If `q` contracts along the restriction of `k` on
sections to the prime of `y`, then the point of `U_X` that `q` cuts out is carried to `y`. -/
theorem IsAffineOpen.apply_fromSpec_of_comap_eq {Y : Scheme.{u}} (k : X ⟶ Y)
    (hU : IsAffineOpen U) {VY : Y.Opens} (hVY : IsAffineOpen VY) (hUV : U ≤ k ⁻¹ᵁ VY)
    (q : PrimeSpectrum Γ(X, U)) {y : Y} (hyV : y ∈ VY)
    (hq : Ideal.comap (k.appLE VY U hUV).hom q.asIdeal =
      (hVY.primeIdealOf ⟨y, hyV⟩).asIdeal) :
    k (hU.fromSpec q) = y := by
  change (hU.fromSpec ≫ k) q = y
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec k hVY hU hUV]
  exact hVY.specMap_fromSpec_apply hyV (k.appLE VY U hUV).hom q hq

/-- **The composite of `Spec D ⟶ Spec Γ(T, W) ≅ W ↪ T` with a morphism `h : T ⟶ S`.** For an
affine open `U` of `S` with `W ≤ h ⁻¹ᵁ U` it is the morphism `Spec D ⟶ Spec Γ(S, U) ≅ U ↪ S`
attached to the restriction of `h` on sections followed by `c`. -/
theorem IsAffineOpen.specMap_fromSpec_comp {S T : Scheme.{u}} (h : T ⟶ S)
    {W : T.Opens} (hW : IsAffineOpen W) {U : S.Opens} (hU : IsAffineOpen U) (hWU : W ≤ h ⁻¹ᵁ U)
    {D : Type u} [CommRing D] (c : Γ(T, W) →+* D) :
    (Spec.map (CommRingCat.ofHom c) ≫ hW.fromSpec) ≫ h =
      Spec.map (CommRingCat.ofHom (c.comp (h.appLE U W hWU).hom)) ≫ hU.fromSpec := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec h hU hW hWU, ← Spec.map_comp_assoc]
  rfl

/-! ### The neighbourhood -/

/-- **The étale neighbourhood an étale algebra over an affine chart determines.** For an affine
open `U ∋ x` of `X`, a ring map `r : Γ(X, U) → D` with étale spectrum and a prime `u` of `D`
contracting to the prime of `x`, the composite `Spec D ⟶ Spec Γ(X, U) ≅ U ↪ X` is étale and
carries `u` to `x`. -/
def IsAffineOpen.etaleNeighborhoodOfChart (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)
    {D : Type u} [CommRing D] (r : Γ(X, U) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    EtaleNeighborhood X x where
  scheme := Spec (CommRingCat.of D)
  point := u
  toBase := Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec
  map_point := hU.specMap_fromSpec_apply hxU r u hu

/-- The scheme of `IsAffineOpen.etaleNeighborhoodOfChart` is `Spec D`. -/
@[simp]
theorem IsAffineOpen.etaleNeighborhoodOfChart_scheme (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)
    {D : Type u} [CommRing D] (r : Γ(X, U) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    (hU.etaleNeighborhoodOfChart hxU r u hu).scheme = Spec (CommRingCat.of D) := rfl

/-- The distinguished point of `IsAffineOpen.etaleNeighborhoodOfChart` is the prime `u`. -/
@[simp]
theorem IsAffineOpen.etaleNeighborhoodOfChart_point (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)
    {D : Type u} [CommRing D] (r : Γ(X, U) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    (hU.etaleNeighborhoodOfChart hxU r u hu).point = u := rfl

/-- The structure morphism of `IsAffineOpen.etaleNeighborhoodOfChart` is the composite
`Spec D ⟶ Spec Γ(X, U) ≅ U ↪ X`. -/
@[simp]
theorem IsAffineOpen.etaleNeighborhoodOfChart_toBase (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)
    {D : Type u} [CommRing D] (r : Γ(X, U) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    (hU.etaleNeighborhoodOfChart hxU r u hu).toBase =
      Spec.map (CommRingCat.ofHom r) ≫ hU.fromSpec := rfl

/-- The scheme of the neighbourhood is affine: it is the spectrum of `D`. -/
instance IsAffineOpen.isAffine_etaleNeighborhoodOfChart (hU : IsAffineOpen U) {x : X}
    (hxU : x ∈ U) {D : Type u} [CommRing D] (r : Γ(X, U) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    IsAffine (hU.etaleNeighborhoodOfChart hxU r u hu).scheme :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of D)))

/-- **The neighbourhood is elementary when the residue field does not grow.** If `r` induces a
bijection of the residue field of the prime of `x` with the residue field of `u`, the residue
field map of the neighbourhood is an isomorphism, which is the defining condition of an
*elementary* étale neighbourhood. -/
theorem IsAffineOpen.isElementary_etaleNeighborhoodOfChart (hU : IsAffineOpen U) {x : X}
    (hxU : x ∈ U) {D : Type u} [CommRing D] (r : Γ(X, U) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)
    (hbij : Function.Bijective
      (Ideal.ResidueField.map (hU.primeIdealOf ⟨x, hxU⟩).asIdeal u.asIdeal r hu.symm)) :
    (hU.etaleNeighborhoodOfChart hxU r u hu).IsElementary := by
  rw [EtaleNeighborhood.isElementary_iff]
  exact isIso_residueFieldMap_chart hU r u (hU.primeIdealOf ⟨x, hxU⟩)
    (PrimeSpectrum.ext hu) hu hbij

/-! ### The map of local rings -/

/-- **The map of local rings of the neighbourhood, read on germs.** Under the canonical
identification of the local ring of `Spec D` at `u` with the localization of `D` there, the map
of local rings of `Spec D ⟶ Spec Γ(X, U) ≅ U ↪ X` carries the germ at `x` of a section
`a : Γ(X, U)` to the image of `r a`. -/
theorem IsAffineOpen.stalkIso_stalkHom_etaleNeighborhoodOfChart_germ (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) {D : Type u} [CommRing D] (r : Γ(X, U) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (a : Γ(X, U)) :
    (Spec.stalkIso (CommRingCat.of D) u).hom.hom
        ((hU.etaleNeighborhoodOfChart hxU r u hu).stalkHom
          ((X.presheaf.germ U x hxU).hom a)) =
      algebraMap D (Localization.AtPrime u.asIdeal) (r a) := by
  have h := congrArg (fun k : Γ(X, U) ⟶ _ => k.hom a)
    (chart_germ_toSpec hU r u x hxU (hU.specMap_fromSpec_apply hxU r u hu))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  rw [show (hU.etaleNeighborhoodOfChart hxU r u hu).stalkHom
      ((X.presheaf.germ U x hxU).hom a) =
      ((Scheme.ΓSpecIso (CommRingCat.of D)).inv ≫
        (Spec (CommRingCat.of D)).presheaf.germ ⊤ u trivial).hom (r a) from h]
  exact stalkIso_hom_germ u (r a)

/-- **The map of local rings of the neighbourhood, as a square with
`Localization.localRingHom`.** For any identification `eX` of `𝒪_{X, x}` with the localization of
the chart ring at the prime of `x` which carries germs to images of sections — the identification
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` supplies — the map of local rings of the
neighbourhood is `Localization.localRingHom` of `r`, read through `eX` and through the canonical
identification of the local ring of `Spec D` at `u`. -/
theorem IsAffineOpen.stalkHom_etaleNeighborhoodOfChart (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) {D : Type u} [CommRing D] (r : Γ(X, U) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (u : PrimeSpectrum D)
    (hu : Ideal.comap r u.asIdeal = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)
    (eX : X.presheaf.stalk x ≃+*
      Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)
    (heX : ∀ a : Γ(X, U), eX ((X.presheaf.germ U x hxU).hom a) =
      algebraMap Γ(X, U) (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) a) :
    (Spec.stalkIso (CommRingCat.of D) u).commRingCatIsoToRingEquiv.toRingHom.comp
        (hU.etaleNeighborhoodOfChart hxU r u hu).stalkHom =
      (Localization.localRingHom (hU.primeIdealOf ⟨x, hxU⟩).asIdeal u.asIdeal r
        hu.symm).comp eX.toRingHom := by
  have hgerm : ∀ a : Γ(X, U), eX.symm
      (algebraMap Γ(X, U) (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) a) =
      (X.presheaf.germ U x hxU).hom a := fun a =>
    eX.injective (by rw [eX.apply_symm_apply, heX])
  have key : ((Spec.stalkIso (CommRingCat.of D) u).commRingCatIsoToRingEquiv.toRingHom.comp
        (hU.etaleNeighborhoodOfChart hxU r u hu).stalkHom).comp
          (eX.symm : _ →+* _) =
      Localization.localRingHom (hU.primeIdealOf ⟨x, hxU⟩).asIdeal u.asIdeal r hu.symm := by
    refine IsLocalization.ringHom_ext (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (RingHom.ext fun a => ?_)
    change (Spec.stalkIso (CommRingCat.of D) u).hom.hom
        ((hU.etaleNeighborhoodOfChart hxU r u hu).stalkHom (eX.symm
          (algebraMap Γ(X, U) (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) a))) = _
    rw [hgerm a, hU.stalkIso_stalkHom_etaleNeighborhoodOfChart_germ hxU r u hu a,
      RingHom.comp_apply, Localization.localRingHom_to_map]
  refine RingHom.ext fun w => ?_
  have hw := RingHom.congr_fun key (eX w)
  simpa using hw

end AlgebraicGeometry

end
