module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.RingTheory.SqZero

/-!
# Scaling the square-zero ideal is an isomorphism over a basic open

Let `R` be a commutative ring and let `Sq R = R ⊕ R` be its square-zero extension
(`Stacks.SqZero.Sq`). Write

* `a : Spec (Sq R) ⟶ Spec R` for the morphism of spectra induced by the structure map
  `R ⟶ Sq R`, and
* `ψ : Spec (Sq R) ⟶ Spec (Sq R)` for the morphism induced by the `R`-algebra endomorphism
  `scale t : (p, q) ↦ (p, t * q)` of `Sq R`.

This file shows that if `t` divides a power of `g : R`, say `t * w = g ^ k`, then the
restriction of `ψ` over the basic open `D(g) ⊆ Spec R` is an isomorphism, even though `ψ`
itself need not be. The point is that `t` becomes invertible after localizing away from `g`,
so `scale t` becomes an automorphism there.

## Main results

* `Stacks.SqZeroScaleIso.bijective_of_scale`: the commutative-algebra heart. If `L` is a
  localization of `Sq R` away from the image of `g` and `θ : L →+* L` extends `scale t`, then
  `θ` is bijective.
* `Stacks.SqZeroScaleIso.isIso_morphismRestrict_specMap_scale`: the geometric conclusion,
  `IsIso (ψ ∣_ (a ⁻¹ᵁ D(g)))`.
* `Stacks.SqZeroScaleIso.isIso_morphismRestrict_specMap_scale_of_eq`: the same conclusion for
  an arbitrary open `Ω` of `Spec R` that happens to equal `D(g)`.

## Implementation notes

The identification of `Γ(Spec (Sq R), a ⁻¹ᵁ D(g))` with a localization of `Sq R` goes through
`AlgebraicGeometry.Scheme.toOpen_eq`, which says that the canonical `Sq R`-algebra structure on
the sections of `Spec (Sq R)` is the restriction map out of the global sections, read through
`AlgebraicGeometry.Scheme.ΓSpecIso`. The instance `Stacks.SqZeroScaleIso.algebraSections` only
restates the algebra structure already present on the structure sheaf in a form whose head
symbol instance search can see.
-/

@[expose] public section

namespace Stacks.SqZeroScaleIso

open CategoryTheory AlgebraicGeometry Stacks.SqZero Stacks.ModuleQuadraticExtension

universe u

noncomputable section

variable {R : Type u} [CommRing R]

/-! ### Elementary identities in the square-zero extension -/

/-- The element `(0, 0)` of the square-zero extension is zero. -/
@[simp] lemma mk_zero_zero : Ext.mk (zeroDatum R) (0 : R) (0 : R) = 0 := by ext <;> simp

/-- The square-zero ideal `0 ⊕ R` of `Sq R` is closed under addition, componentwise. -/
@[simp] lemma mk_zero_add (x y : R) :
    Ext.mk (zeroDatum R) 0 (x + y)
      = Ext.mk (zeroDatum R) 0 x + Ext.mk (zeroDatum R) 0 y := by
  ext <;> simp

/-- Multiplying `(0, q)` by the image of `p : R` scales the second component. -/
lemma algebraMap_mul_mk_zero (p q : R) :
    algebraMap R (Sq R) p * Ext.mk (zeroDatum R) 0 q = Ext.mk (zeroDatum R) 0 (p * q) := by
  rw [Ext.algebraMap_eq]
  ext <;> simp

/-- `scale t` multiplies the square-zero ideal by `t`. -/
lemma scale_mk_zero (t q : R) :
    scale t (Ext.mk (zeroDatum R) 0 q) = Ext.mk (zeroDatum R) 0 (t * q) := by
  ext <;> simp

/-- `scale t` fixes the image of `R` in `Sq R`. -/
lemma scale_algebraMap (t p : R) :
    scale t (algebraMap R (Sq R) p) = algebraMap R (Sq R) p := (scale t).commutes p

/-! ### The twisted lift out of the square-zero extension -/

/-- For an `Sq R`-algebra `L` and an element `u : L`, the ring map `Sq R →+* L` sending `(p, q)`
to `p + u * q`, both components being read in `L` through the structure map.

This is a ring map for *every* `u`, because the ideal `0 ⊕ R` of `Sq R` squares to zero: the
only cross terms that appear in the multiplicativity check are linear in `u`. For `u` the
inverse of the image of `(t, 0)` it is the inverse of the endomorphism induced by `scale t`. -/
def twist (L : Type u) [CommRing L] [Algebra (Sq R) L] (u : L) : Sq R →+* L where
  toFun y := algebraMap (Sq R) L (algebraMap R (Sq R) y.fst)
      + u * algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 y.snd)
  map_one' := by simp
  map_mul' y z := by
    have hz : algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 y.snd)
        * algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 z.snd) = 0 := by
      rw [← map_mul, mk_zero_mul_mk_zero, map_zero]
    have h1 : algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 (y.fst * z.snd))
        = algebraMap (Sq R) L (algebraMap R (Sq R) y.fst)
          * algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 z.snd) := by
      rw [← map_mul, algebraMap_mul_mk_zero]
    have h2 : algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 (z.fst * y.snd))
        = algebraMap (Sq R) L (algebraMap R (Sq R) z.fst)
          * algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 y.snd) := by
      rw [← map_mul, algebraMap_mul_mk_zero]
    simp only [SqZero.fst_mul, SqZero.snd_mul', mk_zero_add, map_add, map_mul, h1, h2]
    linear_combination (-(u * u)) * hz
  map_zero' := by simp
  map_add' y z := by
    simp only [Ext.fst_add, Ext.snd_add, mk_zero_add, map_add]
    ring

/-- The defining formula for `Stacks.SqZeroScaleIso.twist`. -/
lemma twist_apply (L : Type u) [CommRing L] [Algebra (Sq R) L] (u : L) (y : Sq R) :
    twist L u y = algebraMap (Sq R) L (algebraMap R (Sq R) y.fst)
      + u * algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 y.snd) := rfl

/-- `Stacks.SqZeroScaleIso.twist` agrees with the structure map on the image of `R`. -/
lemma twist_algebraMap (L : Type u) [CommRing L] [Algebra (Sq R) L] (u : L) (p : R) :
    twist L u (algebraMap R (Sq R) p) = algebraMap (Sq R) L (algebraMap R (Sq R) p) := by
  rw [twist_apply]
  simp

/-! ### The commutative algebra heart -/

/-- **Scaling the square-zero ideal by `t` is bijective after localizing away from `g`, as soon
as `t` divides a power of `g`.**

Here `L` is a localization of `Sq R` away from the image of `g : R`, and `θ : L →+* L` is any
ring endomorphism of `L` extending the `R`-algebra endomorphism `scale t` of `Sq R`. -/
theorem bijective_of_scale (t g w : R) (k : ℕ) (hgw : t * w = g ^ k)
    (L : Type u) [CommRing L] [Algebra (Sq R) L]
    [IsLocalization.Away (algebraMap R (Sq R) g) L]
    (θ : L →+* L)
    (hθ : ∀ y : Sq R, θ (algebraMap (Sq R) L y) = algebraMap (Sq R) L (scale t y)) :
    Function.Bijective θ := by
  have hprod : Ext.mk (zeroDatum R) t 0 * Ext.mk (zeroDatum R) w 0
      = algebraMap R (Sq R) g ^ k := by
    rw [algebraMap_pow_eq]
    ext
    · simpa using hgw
    · simp
  have hg : IsUnit (algebraMap (Sq R) L (algebraMap R (Sq R) g)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have heu : IsUnit (algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0)) := by
    refine isUnit_of_mul_isUnit_left
      (y := algebraMap (Sq R) L (Ext.mk (zeroDatum R) w 0)) ?_
    rw [← map_mul, hprod, map_pow]
    exact hg.pow k
  obtain ⟨u, hu⟩ : ∃ u : L, u * algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0) = 1 :=
    ⟨(↑heu.unit⁻¹ : L), by rw [mul_comm]; exact heu.mul_val_inv⟩
  have hθe : θ (algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0))
      = algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0) := by
    rw [hθ]
    congr 1
    ext <;> simp
  have hθu : θ u = u := by
    have h1 : algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0) * θ u = 1 := by
      rw [← hθe, ← map_mul, mul_comm, hu, map_one]
    calc θ u = u * algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0) * θ u := by rw [hu, one_mul]
      _ = u * (algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0) * θ u) := by ring
      _ = u := by rw [h1, mul_one]
  have hunits : ∀ y : Submonoid.powers (algebraMap R (Sq R) g),
      IsUnit (twist L u (y : Sq R)) := by
    rintro ⟨-, n, rfl⟩
    rw [map_pow, twist_algebraMap]
    exact hg.pow n
  set θ' : L →+* L := IsLocalization.lift hunits with hθ'
  have key : ∀ q : R, algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 (t * q))
      = algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0)
        * algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 q) := by
    intro q
    rw [← map_mul]
    congr 1
    ext <;> simp
  have hext : ∀ f : L →+* L, (∀ y, f (algebraMap (Sq R) L y) = algebraMap (Sq R) L y) →
      ∀ x, f x = x := fun f hf x => by
    have := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (Sq R) g))
      (j := f) (k := RingHom.id L) (RingHom.ext hf)
    simpa using RingHom.congr_fun this x
  have hleft : ∀ x : L, θ' (θ x) = x :=
    hext (θ'.comp θ) fun y => by
      change θ' (θ (algebraMap (Sq R) L y)) = algebraMap (Sq R) L y
      rw [hθ, hθ', IsLocalization.lift_eq, twist_apply, fst_scale, snd_scale, key,
        ← mul_assoc, hu, one_mul, ← map_add, ← sq_free_snd]
  have hright : ∀ x : L, θ (θ' x) = x :=
    hext (θ.comp θ') fun y => by
      change θ (θ' (algebraMap (Sq R) L y)) = algebraMap (Sq R) L y
      have h1 : θ (algebraMap (Sq R) L (algebraMap R (Sq R) y.fst))
          = algebraMap (Sq R) L (algebraMap R (Sq R) y.fst) := by
        rw [hθ, scale_algebraMap]
      have h2 : θ (algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 y.snd))
          = algebraMap (Sq R) L (Ext.mk (zeroDatum R) t 0)
            * algebraMap (Sq R) L (Ext.mk (zeroDatum R) 0 y.snd) := by
        rw [hθ, scale_mk_zero, key]
      rw [hθ', IsLocalization.lift_eq, twist_apply, map_add, map_mul, hθu, h1, h2,
        ← mul_assoc, hu, one_mul, ← map_add, ← sq_free_snd]
  exact ⟨Function.LeftInverse.injective hleft, fun x => ⟨θ' x, hright x⟩⟩

/-! ### The two morphisms of spectra -/

variable (R) in
/-- The morphism `Spec (Sq R) ⟶ Spec R` induced by the structure map `R ⟶ Sq R`. -/
def specAug : Spec (CommRingCat.of (Sq R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Sq R)))

/-- The endomorphism of `Spec (Sq R)` induced by `Stacks.SqZero.scale t`. -/
def specScale (t : R) : Spec (CommRingCat.of (Sq R)) ⟶ Spec (CommRingCat.of (Sq R)) :=
  Spec.map (CommRingCat.ofHom (scale t : Sq R →ₐ[R] Sq R).toRingHom)

/-- Scaling lies over the identity of `Spec R`, because `scale t` is an `R`-algebra map. -/
lemma specScale_comp_specAug (t : R) : specScale t ≫ specAug R = specAug R := by
  have h : (scale t : Sq R →ₐ[R] Sq R).toRingHom.comp (algebraMap R (Sq R))
      = algebraMap R (Sq R) := RingHom.ext fun r => (scale t).commutes r
  rw [specScale, specAug, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- Scaling preserves every open pulled back from `Spec R`. -/
lemma specScale_preimage (t : R) (Ω : (Spec (CommRingCat.of R)).Opens) :
    specScale t ⁻¹ᵁ (specAug R ⁻¹ᵁ Ω) = specAug R ⁻¹ᵁ Ω := by
  rw [← Scheme.Hom.comp_preimage, specScale_comp_specAug]

/-- The preimage under `Stacks.SqZeroScaleIso.specAug` of the basic open `D(g)` is the basic
open of the image of `g` in `Sq R`. -/
lemma specAug_preimage_basicOpen (g : R) :
    specAug R ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of R)).Opens)
      = PrimeSpectrum.basicOpen (algebraMap R (Sq R) g) :=
  SpecMap_preimage_basicOpen _ _

/-! ### Sections of `Spec (Sq R)` as a localization -/

/-- The canonical algebra structure of a ring `A` on the sections of `Spec A` over an open,
restated so that instance search finds it for `Γ(Spec (CommRingCat.of A), U)`. It is the
algebra structure of the structure sheaf, i.e. the restriction of global sections. -/
instance algebraSections (A : Type u) [CommRing A] (U : (Spec (CommRingCat.of A)).Opens) :
    Algebra A Γ(Spec (CommRingCat.of A), U) :=
  inferInstanceAs (Algebra A ((Spec.structureSheaf A).obj.obj (Opposite.op U)))

/-- The structure map `A ⟶ Γ(Spec A, U)` is the restriction of global sections along
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
lemma ofHom_algebraMap_sections (A : Type u) [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) :
    CommRingCat.ofHom (algebraMap A Γ(Spec (CommRingCat.of A), U))
      = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op :=
  Scheme.toOpen_eq (CommRingCat.of A) U

/-- **The sections of `Spec (Sq R)` over `a ⁻¹ᵁ D(g)` are the localization of `Sq R` away from
the image of `g`.** -/
instance isLocalization_sections (g : R) :
    IsLocalization.Away (algebraMap R (Sq R) g)
      Γ(Spec (CommRingCat.of (Sq R)),
        specAug R ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of R)).Opens)) :=
  inferInstanceAs (IsLocalization.Away (algebraMap R (Sq R) g)
    ((Spec.structureSheaf (Sq R)).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen (algebraMap R (Sq R) g)))))

/-! ### The induced endomorphism of sections -/

/-- The endomorphism of `Γ(Spec (Sq R), a ⁻¹ᵁ Ω)` induced by `Spec (scale t)`, which preserves
this open by `Stacks.SqZeroScaleIso.specScale_preimage`. -/
def sectionsScale (t : R) (Ω : (Spec (CommRingCat.of R)).Opens) :
    Γ(Spec (CommRingCat.of (Sq R)), specAug R ⁻¹ᵁ Ω) ⟶
      Γ(Spec (CommRingCat.of (Sq R)), specAug R ⁻¹ᵁ Ω) :=
  (specScale t).appLE _ _ (specScale_preimage t Ω).ge

/-- `Stacks.SqZeroScaleIso.sectionsScale` is `Spec (scale t)` on sections: composed with the
structure map of `Sq R` it is `scale t` followed by the structure map. -/
lemma algebraMap_comp_sectionsScale (t : R) (Ω : (Spec (CommRingCat.of R)).Opens) :
    CommRingCat.ofHom
          (algebraMap (Sq R) Γ(Spec (CommRingCat.of (Sq R)), specAug R ⁻¹ᵁ Ω))
        ≫ sectionsScale t Ω
      = CommRingCat.ofHom (scale t : Sq R →ₐ[R] Sq R).toRingHom
        ≫ CommRingCat.ofHom
          (algebraMap (Sq R) Γ(Spec (CommRingCat.of (Sq R)), specAug R ⁻¹ᵁ Ω)) := by
  rw [ofHom_algebraMap_sections, sectionsScale, Category.assoc,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE, Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- `Stacks.SqZeroScaleIso.sectionsScale` extends `Stacks.SqZero.scale`. -/
lemma sectionsScale_algebraMap (t : R) (Ω : (Spec (CommRingCat.of R)).Opens) (y : Sq R) :
    sectionsScale t Ω (algebraMap (Sq R) _ y)
      = algebraMap (Sq R) Γ(Spec (CommRingCat.of (Sq R)), specAug R ⁻¹ᵁ Ω) (scale t y) :=
  congr($(algebraMap_comp_sectionsScale t Ω) y)

/-! ### The isomorphism -/

/-- The induced endomorphism of the sections over `a ⁻¹ᵁ D(g)` is an isomorphism. -/
theorem isIso_sectionsScale (t g w : R) (k : ℕ) (hgw : t * w = g ^ k) :
    IsIso (sectionsScale t (PrimeSpectrum.basicOpen g)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_of_scale t g w k hgw _ (sectionsScale t (PrimeSpectrum.basicOpen g)).hom
      fun y => sectionsScale_algebraMap t _ y)

/-- The map on sections over `a ⁻¹ᵁ D(g)` induced by `Spec (scale t)` is an isomorphism. -/
theorem isIso_app_specScale (t g w : R) (k : ℕ) (hgw : t * w = g ^ k) :
    IsIso ((specScale t).app
      (specAug R ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of R)).Opens))) := by
  have h := specScale_preimage t (PrimeSpectrum.basicOpen g)
  have hiso : IsIso ((Spec (CommRingCat.of (Sq R))).presheaf.map (homOfLE h.ge).op) := by
    rw [show homOfLE h.ge = eqToHom h.symm from Subsingleton.elim _ _]
    infer_instance
  have hcomp : IsIso ((specScale t).app
        (specAug R ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of R)).Opens)) ≫
      (Spec (CommRingCat.of (Sq R))).presheaf.map (homOfLE h.ge).op) :=
    isIso_sectionsScale t g w k hgw
  exact IsIso.of_isIso_comp_right _ ((Spec (CommRingCat.of (Sq R))).presheaf.map (homOfLE h.ge).op)

/-- **Scaling the square-zero ideal by `t` restricts to an isomorphism over `D(g)` whenever `t`
divides a power of `g`.**

Here `ψ = Spec (scale t)` and `a = Spec (algebraMap R (Sq R))`; the hypothesis is
`t * w = g ^ k`. -/
theorem isIso_morphismRestrict_specMap_scale (t g w : R) (k : ℕ) (hgw : t * w = g ^ k) :
    IsIso (Spec.map (CommRingCat.ofHom (scale t : Sq R →ₐ[R] Sq R).toRingHom) ∣_
      (Spec.map (CommRingCat.ofHom (algebraMap R (Sq R))) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of R)).Opens))) :=
  (isIso_morphismRestrict_iff_isIso_app _
      ((IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) g).preimage _)).mpr
    (isIso_app_specScale t g w k hgw)

/-- The form of `Stacks.SqZeroScaleIso.isIso_morphismRestrict_specMap_scale` taking an
arbitrary open `Ω` of `Spec R` equal to a basic open. -/
theorem isIso_morphismRestrict_specMap_scale_of_eq (t g w : R) (k : ℕ) (hgw : t * w = g ^ k)
    (Ω : (Spec (CommRingCat.of R)).Opens) (hΩ : Ω = PrimeSpectrum.basicOpen g) :
    IsIso (Spec.map (CommRingCat.ofHom (scale t : Sq R →ₐ[R] Sq R).toRingHom) ∣_
      (Spec.map (CommRingCat.ofHom (algebraMap R (Sq R))) ⁻¹ᵁ Ω)) := by
  subst hΩ
  exact isIso_morphismRestrict_specMap_scale t g w k hgw

end

end Stacks.SqZeroScaleIso

end
