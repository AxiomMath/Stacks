module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.AffineOfKrullDimLEOne
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Finiteness

/-!
# Affineness of the punctured spectrum of a Noetherian local ring

For a Noetherian local ring `A`, the punctured spectrum `Spec A \ {m}` is an affine open subscheme
of `Spec A` exactly when `A` has Krull dimension at most one.

The implication from dimension at most one to affineness is
`Stacks.PuncturedSpectrum.isAffineOpen_puncturedSpectrum_of_krullDimLE_one`, and the algebraic
content of the converse is
`Stacks.PuncturedSpectrum.krullDimLE_one_of_isPuncturedSpectrumAlgebra`. This file supplies the
bridge between the two: if the punctured spectrum `U` is affine, then its ring of sections
`B = Γ(Spec A, U)` is a Noetherian `A`-algebra whose spectrum maps isomorphically onto `U`, and
every section is carried into `A` by a power of any given element of the maximal ideal.

The equivalence of the two conditions, Stacks Tag 0BCR, is assembled from its two implications in
`Stacks.Divisors.isAffineOpen_puncturedSpectrum_iff_krullDimLE_one`.

## Main results

* `Stacks.PuncturedSpectrum.range_comap_algebraMap_of_isAffineOpen`: for an affine open `U` of
  `Spec R`, the image of `Spec Γ(Spec R, U) → Spec R` is `U`.
* `Stacks.PuncturedSpectrum.exists_pow_smul_mem_range_of_basicOpen_le`: if `D(g)` is contained in
  an affine open `U` of `Spec R`, then a power of `g` carries any section over `U` into the image
  of `R`.
* `Stacks.PuncturedSpectrum.krullDimLE_one_of_isAffineOpen_puncturedSpectrum`: if the punctured
  spectrum of a Noetherian local ring is affine, then the ring has Krull dimension at most one.

## Implementation notes

The identification of `Spec Γ(Spec R, U) → Spec R` with `Spec` of the canonical ring map
`R → Γ(Spec R, U)` comes from `AlgebraicGeometry.IsAffineOpen.fromSpec_toSpecΓ` together with
`AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv`, which says that `(Spec R).toSpecΓ` is inverted
by `Spec` of `Scheme.ΓSpecIso`.

For the second result, write `f` for the image of `g` in `Γ(Spec R, U)`. The basic open set of
`f` is `U ⊓ D(g) = D(g)`, so the sections over `D(g)` are simultaneously the localization of
`Γ(Spec R, U)` at `f` and the localization of `R` at `g`. Writing the image of a section as a
fraction over `R` and clearing the resulting `f`-torsion gives the required power of `g`.

No use is made of the affineness of thickenings (Stacks tag 06AD); the hard direction goes
through `Stacks.PuncturedSpectrum.krullDimLE_one_of_isPuncturedSpectrumAlgebra` directly.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.PuncturedSpectrum

/-- For an affine open `U` of `Spec R`, the canonical morphism `Spec Γ(Spec R, U) ⟶ Spec R` is
`Spec` of the restriction map `R → Γ(Spec R, U)`. -/
theorem fromSpec_eq_SpecMap_algebraMap {R : CommRingCat.{u}} {U : (Spec R).Opens}
    (hU : IsAffineOpen U) :
    hU.fromSpec = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, U))) := by
  have h1 : hU.fromSpec ≫ (Spec R).toSpecΓ =
      Spec.map ((Spec R).presheaf.map (homOfLE le_top).op) := hU.fromSpec_toSpecΓ
  calc hU.fromSpec = hU.fromSpec ≫ ((Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv) := by
        rw [AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = Spec.map ((Spec R).presheaf.map (homOfLE le_top).op) ≫
          Spec.map (Scheme.ΓSpecIso R).inv := by rw [← Category.assoc, h1]
    _ = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, U))) := by
        rw [← Spec.map_comp]
        rfl

/-- For an affine open `U` of `Spec R`, the image of the map on spectra induced by the restriction
map `R → Γ(Spec R, U)` is exactly `U`. -/
theorem range_comap_algebraMap_of_isAffineOpen {R : CommRingCat.{u}} {U : (Spec R).Opens}
    (hU : IsAffineOpen U) :
    Set.range (PrimeSpectrum.comap (algebraMap R Γ(Spec R, U))) = (U : Set (Spec R)) := by
  rw [← hU.range_fromSpec, fromSpec_eq_SpecMap_algebraMap hU]
  rfl

/-- If the basic open set of `g : R` is contained in an affine open `U` of `Spec R`, then some
power of `g` carries any section over `U` into the image of `R`. -/
theorem exists_pow_smul_mem_range_of_basicOpen_le {R : CommRingCat.{u}} {U : (Spec R).Opens}
    (hU : IsAffineOpen U) (g : R) (hg : PrimeSpectrum.basicOpen g ≤ U) (b : Γ(Spec R, U)) :
    ∃ k : ℕ, g ^ k • b ∈ LinearMap.range (Algebra.linearMap R Γ(Spec R, U)) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : Γ(Spec R, U), f = algebraMap R Γ(Spec R, U) g := ⟨_, rfl⟩
  have hV : (Spec R).basicOpen f = PrimeSpectrum.basicOpen g := by
    have h : f = (Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv g) := hf
    rw [h, Scheme.basicOpen_res, basicOpen_eq_of_affine]
    exact inf_eq_right.mpr hg
  have haway : ∀ W : (Spec R).Opens, W = PrimeSpectrum.basicOpen g →
      IsLocalization.Away g Γ(Spec R, W) := by
    rintro W rfl
    infer_instance
  have i1 : IsLocalization.Away f Γ(Spec R, (Spec R).basicOpen f) :=
    hU.isLocalization_basicOpen f
  have i2 : IsLocalization.Away g Γ(Spec R, (Spec R).basicOpen f) := haway _ hV
  have hcomp : ∀ x : R, algebraMap Γ(Spec R, U) Γ(Spec R, (Spec R).basicOpen f)
      (algebraMap R Γ(Spec R, U) x) =
        algebraMap R Γ(Spec R, (Spec R).basicOpen f) x := fun _ => rfl
  obtain ⟨n, a, hs⟩ := IsLocalization.Away.surj (S := Γ(Spec R, (Spec R).basicOpen f)) g
    (algebraMap Γ(Spec R, U) _ b)
  have key : algebraMap Γ(Spec R, U) Γ(Spec R, (Spec R).basicOpen f)
        (b * algebraMap R Γ(Spec R, U) (g ^ n)) =
      algebraMap Γ(Spec R, U) Γ(Spec R, (Spec R).basicOpen f)
        (algebraMap R Γ(Spec R, U) a) := by
    rw [map_mul, hcomp, hcomp, map_pow]
    exact hs
  obtain ⟨m, hc⟩ := IsLocalization.Away.exists_of_eq (S := Γ(Spec R, (Spec R).basicOpen f))
    (x := f) key
  refine ⟨n + m, g ^ m * a, ?_⟩
  simp only [map_pow, ← hf] at hc
  simp only [Algebra.linearMap_apply, Algebra.smul_def, map_mul, map_pow, ← hf]
  rw [← hc]
  ring

/-- If an affine open `U` of `Spec R` is the complement of the closed point of a Noetherian local
ring `R`, then `R` has Krull dimension at most one. -/
private theorem krullDimLE_one_of_isAffineOpen_aux (R : CommRingCat.{u}) [IsLocalRing R]
    [IsNoetherianRing R] (U : (Spec R).Opens) (hU : IsAffineOpen U)
    (hUeq : ∀ p : PrimeSpectrum R, p ∈ U ↔ p ≠ IsLocalRing.closedPoint R) :
    Ring.KrullDimLE 1 R := by
  have _ : IsNoetherianRing ↥Γ(Spec R, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hgle : ∀ g ∈ IsLocalRing.maximalIdeal R, PrimeSpectrum.basicOpen g ≤ U := by
    intro g hgm p hp
    refine (hUeq p).mpr fun hpc => ?_
    subst hpc
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hp hgm
  refine krullDimLE_one_of_isPuncturedSpectrumAlgebra ↥R ↥Γ(Spec R, U) ?_ ?_
  · rw [range_comap_algebraMap_of_isAffineOpen hU]
    exact Set.ext hUeq
  · exact fun g hgm => exists_pow_smul_mem_range_of_basicOpen_le hU g (hgle g hgm)

/-- If the punctured spectrum of a Noetherian local ring `A` is an affine open, then `A` has
Krull dimension at most one. -/
theorem krullDimLE_one_of_isAffineOpen_puncturedSpectrum (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hU : IsAffineOpen (Stacks.puncturedSpectrum A)) :
    Ring.KrullDimLE 1 A :=
  krullDimLE_one_of_isAffineOpen_aux (CommRingCat.of A) (Stacks.puncturedSpectrum A) hU
    fun _ => Iff.rfl

end Stacks.PuncturedSpectrum

end
