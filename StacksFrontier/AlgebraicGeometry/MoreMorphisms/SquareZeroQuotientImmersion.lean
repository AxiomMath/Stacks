module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Square-zero closed immersions between quotient spectra

The kernel ideal sheaf of a morphism into an affine scheme is determined by the kernel of the
map of global sections, so for a morphism of affine spectra it is determined by the kernel of
the ring map. Consequently the closed immersion `Spec (R ⧸ J) ↪ Spec (R ⧸ I)` attached to an
inclusion `I ≤ J` of ideals is defined by a square-zero ideal exactly when `J ^ 2 ≤ I`.

## Main results

* `AlgebraicGeometry.ker_pow_eq_bot_iff_of_isAffine`: a power of the kernel ideal sheaf of a
  morphism into an affine scheme vanishes exactly when the corresponding power of the kernel
  of the map of global sections does.
* `AlgebraicGeometry.ker_pow_spec_map_eq_bot_iff`: the same for a morphism of spectra, in terms
  of the kernel of the ring map.
* `AlgebraicGeometry.isClosedImmersion_spec_map_quotientFactor` and
  `AlgebraicGeometry.ker_sq_spec_map_quotientFactor_eq_bot`: the quotient comparison morphism
  is a closed immersion, and is defined by a square-zero ideal when `J ^ 2 ≤ I`.

## References

* [Stacks Project, Tag 01QO](https://stacks.math.columbia.edu/tag/01QO)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Ideal.Quotient

/-- The kernel of the comparison map `R ⧸ I → R ⧸ J` of quotients by nested ideals is the
image of the larger ideal. -/
public theorem ker_factor {R : Type u} [CommRing R] {I J : Ideal R} (h : I ≤ J) :
    RingHom.ker (Ideal.Quotient.factor h) = J.map (Ideal.Quotient.mk I) := by
  have hcomp : Ideal.comap (Ideal.Quotient.mk I) (RingHom.ker (Ideal.Quotient.factor h)) = J := by
    rw [RingHom.comap_ker, Ideal.Quotient.factor_comp_mk, Ideal.mk_ker]
  exact (Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (RingHom.ker (Ideal.Quotient.factor h))).symm.trans
      (congrArg (Ideal.map (Ideal.Quotient.mk I)) hcomp)

end Ideal.Quotient

namespace AlgebraicGeometry

/-- A power of the kernel ideal sheaf of a morphism into an affine scheme vanishes exactly
when the corresponding power of the kernel of the induced map of global sections does. -/
public theorem ker_pow_eq_bot_iff_of_isAffine {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    (n : ℕ) : f.ker ^ n = ⊥ ↔ (RingHom.ker f.appTop.hom) ^ n = ⊥ := by
  rw [Scheme.ker_of_isAffine]
  constructor
  · intro h
    simpa using congrArg (Scheme.IdealSheafData.equivOfIsAffine (X := Y)) h
  · intro h
    exact (Scheme.IdealSheafData.equivOfIsAffine (X := Y)).injective (by simpa using h)

/-- The global sections of a morphism of spectra are the ring map read through the canonical
identifications. -/
public theorem appTop_spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (Spec.map φ).appTop = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The kernel of the map of global sections of a morphism of spectra is the kernel of the
ring map, pulled back along the canonical identification of the source. -/
public theorem ker_appTop_spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    RingHom.ker (Spec.map φ).appTop.hom =
      Ideal.comap (Scheme.ΓSpecIso A).hom.hom (RingHom.ker φ.hom) := by
  have hinj : Function.Injective (Scheme.ΓSpecIso B).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1
  ext x
  rw [appTop_spec_map]
  simp only [RingHom.mem_ker, Ideal.mem_comap, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  exact ⟨fun hx => hinj (by simpa using hx), fun hx => by rw [hx, map_zero]⟩

/-- A power of the kernel ideal sheaf of a morphism of spectra vanishes exactly when the
corresponding power of the kernel of the ring map does. -/
public theorem ker_pow_spec_map_eq_bot_iff {A B : CommRingCat.{u}} (φ : A ⟶ B) (n : ℕ) :
    (Spec.map φ).ker ^ n = ⊥ ↔ (RingHom.ker φ.hom) ^ n = ⊥ := by
  have hsurj : Function.Surjective (Scheme.ΓSpecIso A).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).2
  have hker : RingHom.ker (Scheme.ΓSpecIso A).hom.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1
  rw [ker_pow_eq_bot_iff_of_isAffine, ker_appTop_spec_map]
  have key : Ideal.map (Scheme.ΓSpecIso A).hom.hom
      ((Ideal.comap (Scheme.ΓSpecIso A).hom.hom (RingHom.ker φ.hom)) ^ n) =
      (RingHom.ker φ.hom) ^ n := by
    rw [Ideal.map_pow, Ideal.map_comap_of_surjective _ hsurj]
  constructor
  · intro hb
    rw [← key, hb, Ideal.map_bot]
  · intro hb
    have hz : Ideal.map (Scheme.ΓSpecIso A).hom.hom
        ((Ideal.comap (Scheme.ΓSpecIso A).hom.hom (RingHom.ker φ.hom)) ^ n) = ⊥ := by
      rw [key, hb]
    rw [Ideal.map_eq_bot_iff_le_ker, hker, le_bot_iff] at hz
    exact hz

/-- The comparison morphism `Spec (R ⧸ J) ⟶ Spec (R ⧸ I)` of quotients by nested ideals is a
closed immersion. -/
public theorem isClosedImmersion_spec_map_quotientFactor {R : Type u} [CommRing R]
    {I J : Ideal R} (h : I ≤ J) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) :=
  IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective h)

/-- **The comparison morphism of quotients by nested ideals is defined by a square-zero ideal
when the larger ideal has square inside the smaller one.** Its kernel ideal sheaf is the image
of `J` in `R ⧸ I`, whose square is the image of `J ^ 2`. -/
public theorem ker_sq_spec_map_quotientFactor_eq_bot {R : Type u} [CommRing R]
    {I J : Ideal R} (h : I ≤ J) (hsq : J ^ 2 ≤ I) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).ker ^ 2 = ⊥ := by
  rw [ker_pow_spec_map_eq_bot_iff]
  have hker : RingHom.ker (CommRingCat.ofHom (Ideal.Quotient.factor h)).hom =
      J.map (Ideal.Quotient.mk I) := Ideal.Quotient.ker_factor h
  rw [hker, ← Ideal.map_pow, le_bot_iff.mp
    ((Ideal.map_mono hsq).trans (Ideal.map_quotient_self I).le)]

end AlgebraicGeometry

end
