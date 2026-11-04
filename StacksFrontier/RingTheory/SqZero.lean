module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.ModuleQuadraticExtension

/-!
# The square-zero extension `R ⊕ R` as a quadratic extension

This file specializes `Stacks.ModuleQuadraticExtension.Ext` to the quadratic datum on `M = R`
whose form vanishes identically: the resulting ring `Sq R` is `R ⊕ R` with the multiplication
`(a, x) * (b, y) = (a * b, a * y + b * x)`, i.e. the ring of dual numbers `R[ε] / (ε ^ 2)`.

## Main definitions

* `Stacks.SqZero.zeroDatum`: the quadratic datum on `M = R` with vanishing form.
* `Stacks.SqZero.Sq`: the square-zero extension `R ⊕ R`.
* `Stacks.SqZero.aug`: the augmentation `Sq R →+* R`, `(a, x) ↦ a`.
* `Stacks.SqZero.scale` and `Stacks.SqZero.scaleEquiv`: the `R`-algebra endomorphism
  `(a, x) ↦ (a, t * x)` of `Sq R`, and the automorphism it is when `t` is a unit.
* `Stacks.SqZero.mapSq`: the ring map `Sq R →+* Sq S` induced by an `R`-algebra `S`.

## Main results

* `Stacks.SqZero.isIntegralHom_specMap_algebraMap` and
  `Stacks.SqZero.surjective_specMap_algebraMap`: `Spec (Sq R) ⟶ Spec R` is integral and
  surjective.
* `Stacks.SqZero.isLocalization_away_sq`: forming `Sq` commutes with localization away from an
  element, `Sq R_g` being the localization of `Sq R` away from the image of `g`. This is what
  makes `R ↦ Sq R` the sections of a quasi-coherent algebra on `Spec R`.
-/

@[expose] public section

namespace Stacks.SqZero

open CategoryTheory AlgebraicGeometry Stacks.ModuleQuadraticExtension

universe u

noncomputable section

variable {R : Type u} [CommRing R]

/-! ### The datum with vanishing form -/

/-- The quadratic datum on the module `M = R` whose form is identically zero. The associated
quadratic extension is the square-zero extension `R ⊕ R`. -/
def zeroDatum (R : Type u) [CommRing R] : QuadraticDatum R R where
  form := 0
  form_comm _ _ := rfl
  smul_form _ _ _ := by simp

/-- The form of `Stacks.SqZero.zeroDatum` vanishes. -/
@[simp] lemma zeroDatum_form_apply (R : Type u) [CommRing R] (x y : R) :
    (zeroDatum R).form x y = 0 := rfl

/-- The *square-zero extension* of `R`: the `R`-algebra `R ⊕ R` with the multiplication
`(a, x) * (b, y) = (a * b, a * y + b * x)`, i.e. `R[ε] / (ε ^ 2)`. -/
abbrev Sq (R : Type u) [CommRing R] : Type u := Ext (zeroDatum R)

/-- The first component of a product in `Sq R` is the product of the first components. -/
@[simp] lemma fst_mul (y z : Sq R) : (y * z).fst = y.fst * z.fst := by
  simp

/-- The second component of a product in `Sq R`. -/
@[simp] lemma snd_mul (y z : Sq R) : (y * z).snd = y.fst • z.snd + z.fst • y.snd := rfl

/-- The second component of a product in `Sq R`, written multiplicatively. -/
lemma snd_mul' (y z : Sq R) : (y * z).snd = y.fst * z.snd + z.fst * y.snd := rfl

/-- Every element of `Sq R` is the sum of its first component, viewed in `R`, and its second
component, viewed in the square-zero ideal. -/
lemma sq_free_snd (y : Sq R) :
    y = algebraMap R (Sq R) y.fst + Ext.mk (zeroDatum R) 0 y.snd := by
  ext
  · simp
  · simp

/-- The ideal `0 ⊕ R` of `Sq R` squares to zero. -/
lemma mk_zero_mul_mk_zero (x y : R) :
    Ext.mk (zeroDatum R) 0 x * Ext.mk (zeroDatum R) 0 y = 0 := by
  ext
  · simp
  · simp

/-- An element of `Sq R` whose first component is a unit is a unit: the inverse of `(a, x)` is
`(a⁻¹, -a⁻¹ ^ 2 * x)`. -/
lemma isUnit_mk {T : Type u} [CommRing T] {a : T} (ha : IsUnit a) (x : T) :
    IsUnit (Ext.mk (zeroDatum T) a x) := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have key : Ext.mk (zeroDatum T) a x * Ext.mk (zeroDatum T) b (-(b * b) * x) = 1 := by
    ext
    · simpa using hb
    · show a • (-(b * b) * x) + b • x = (0 : T)
      simp only [smul_eq_mul]
      linear_combination (-(b * x)) * hb
  exact ⟨⟨_, _, key, by rw [mul_comm]; exact key⟩, rfl⟩

/-! ### The augmentation -/

/-- The augmentation `Sq R →+* R`, `(a, x) ↦ a`, which splits the structure map. -/
def aug (R : Type u) [CommRing R] : Sq R →+* R where
  toFun y := y.fst
  map_one' := rfl
  map_mul' y z := by simp
  map_zero' := rfl
  map_add' y z := rfl

/-- The augmentation is the first projection. -/
@[simp] lemma aug_apply (y : Sq R) : aug R y = y.fst := rfl

/-- The augmentation undoes the structure map. -/
@[simp] lemma aug_algebraMap (r : R) : aug R (algebraMap R (Sq R) r) = r := by simp

/-- The augmentation is a retraction of the structure map. -/
lemma aug_comp_algebraMap :
    (aug R).comp (algebraMap R (Sq R)) = RingHom.id R := by
  ext r
  simp

/-! ### Scaling the square-zero ideal -/

/-- The `R`-algebra endomorphism `(a, x) ↦ (a, t * x)` of `Sq R`. -/
def scale {R : Type u} [CommRing R] (t : R) : Sq R →ₐ[R] Sq R where
  toFun y := Ext.mk (zeroDatum R) y.fst (t * y.snd)
  map_one' := by ext <;> simp
  map_mul' y z := by
    ext
    · simp
    · change t * (y.fst • z.snd + z.fst • y.snd)
        = y.fst • (t * z.snd) + z.fst • (t * y.snd)
      simp only [smul_eq_mul]
      ring
  map_zero' := by ext <;> simp
  map_add' y z := by
    ext
    · simp
    · change t * (y.snd + z.snd) = t * y.snd + t * z.snd
      ring
  commutes' r := by
    ext
    · simp
    · change t * (0 : R) = 0
      simp

/-- Scaling does not change the first component. -/
@[simp] lemma fst_scale (t : R) (y : Sq R) : (scale t y).fst = y.fst := rfl

/-- Scaling multiplies the second component by `t`. -/
@[simp] lemma snd_scale (t : R) (y : Sq R) : (scale t y).snd = t * y.snd := rfl

/-- Scaling by a unit is an `R`-algebra automorphism of `Sq R`. -/
def scaleEquiv {R : Type u} [CommRing R] {t : R} (ht : IsUnit t) : Sq R ≃ₐ[R] Sq R :=
  AlgEquiv.ofAlgHom (scale t) (scale (↑ht.unit⁻¹ : R))
    (AlgHom.ext fun y => Ext.ext' rfl (by
      change t * ((↑ht.unit⁻¹ : R) * y.snd) = y.snd
      rw [← mul_assoc, ht.mul_val_inv, one_mul]))
    (AlgHom.ext fun y => Ext.ext' rfl (by
      change (↑ht.unit⁻¹ : R) * (t * y.snd) = y.snd
      rw [← mul_assoc, mul_comm _ t, ht.mul_val_inv, one_mul]))

/-- `Stacks.SqZero.scaleEquiv` is given by `Stacks.SqZero.scale`. -/
@[simp] lemma scaleEquiv_apply {t : R} (ht : IsUnit t) (y : Sq R) :
    scaleEquiv ht y = scale t y := rfl

/-- The underlying algebra map of `Stacks.SqZero.scaleEquiv` is `Stacks.SqZero.scale`. -/
@[simp] lemma scaleEquiv_toAlgHom {t : R} (ht : IsUnit t) :
    (scaleEquiv ht : Sq R ≃ₐ[R] Sq R).toAlgHom = scale t := rfl

/-! ### Functoriality and localization -/

variable (Rg : Type u) [CommRing Rg] [Algebra R Rg]

/-- The ring map `Sq R →+* Sq Rg` induced by an `R`-algebra `Rg`, applying `algebraMap R Rg`
to both components. -/
def mapSq {R : Type u} [CommRing R] (Rg : Type u) [CommRing Rg] [Algebra R Rg] :
    Sq R →+* Sq Rg where
  toFun y := Ext.mk (zeroDatum Rg) (algebraMap R Rg y.fst) (algebraMap R Rg y.snd)
  map_one' := by ext <;> simp
  map_mul' y z := by
    ext
    · simp
    · change algebraMap R Rg (y.fst • z.snd + z.fst • y.snd)
        = algebraMap R Rg y.fst • algebraMap R Rg z.snd
          + algebraMap R Rg z.fst • algebraMap R Rg y.snd
      simp only [smul_eq_mul, map_add, map_mul]
  map_zero' := by ext <;> simp
  map_add' y z := by ext <;> simp

/-- `Stacks.SqZero.mapSq` acts on the first component by `algebraMap R Rg`. -/
@[simp] lemma fst_mapSq (y : Sq R) : (mapSq Rg y).fst = algebraMap R Rg y.fst := rfl

/-- `Stacks.SqZero.mapSq` acts on the second component by `algebraMap R Rg`. -/
@[simp] lemma snd_mapSq (y : Sq R) : (mapSq Rg y).snd = algebraMap R Rg y.snd := rfl

/-- `Sq Rg` is an algebra over `Sq R` via `Stacks.SqZero.mapSq`. -/
instance algebraSq : Algebra (Sq R) (Sq Rg) := (mapSq Rg).toAlgebra

/-- The structure map of `Stacks.SqZero.algebraSq` is `Stacks.SqZero.mapSq`. -/
lemma algebraMap_sq (y : Sq R) : algebraMap (Sq R) (Sq Rg) y = mapSq Rg y := rfl

/-- The first component of the image of `y` in `Sq Rg`. -/
@[simp] lemma fst_algebraMap_sq (y : Sq R) :
    (algebraMap (Sq R) (Sq Rg) y).fst = algebraMap R Rg y.fst := rfl

/-- The second component of the image of `y` in `Sq Rg`. -/
@[simp] lemma snd_algebraMap_sq (y : Sq R) :
    (algebraMap (Sq R) (Sq Rg) y).snd = algebraMap R Rg y.snd := rfl

/-- The two routes `R → Sq R → Sq Rg` and `R → Rg → Sq Rg` agree. -/
lemma algebraMap_sq_algebraMap (g : R) :
    algebraMap (Sq R) (Sq Rg) (algebraMap R (Sq R) g)
      = algebraMap Rg (Sq Rg) (algebraMap R Rg g) := by
  ext
  · simp
  · simp

/-- A power of the image of `g : R` in `Sq R` is the element `(g ^ k, 0)`. -/
lemma algebraMap_pow_eq (g : R) (k : ℕ) :
    algebraMap R (Sq R) g ^ k = Ext.mk (zeroDatum R) (g ^ k) 0 := by
  rw [← map_pow, Ext.algebraMap_eq]

/-- A power of the image of `g : R` in `Sq Rg` is the element `(g ^ k, 0)`. -/
lemma algebraMap_sq_algebraMap_pow (g : R) (k : ℕ) :
    algebraMap (Sq R) (Sq Rg) (algebraMap R (Sq R) g) ^ k
      = Ext.mk (zeroDatum Rg) (algebraMap R Rg g ^ k) 0 := by
  rw [algebraMap_sq_algebraMap, algebraMap_pow_eq]

/-- **Forming the square-zero extension commutes with localization away from an element.**
If `Rg` is the localization of `R` away from `g`, then `Sq Rg` is the localization of `Sq R`
away from the image of `g`. -/
theorem isLocalization_away_sq {R : Type u} [CommRing R] (g : R)
    (Rg : Type u) [CommRing Rg] [Algebra R Rg] [IsLocalization.Away g Rg] :
    IsLocalization.Away (algebraMap R (Sq R) g) (Sq Rg) := by
  refine IsLocalization.Away.mk _ ?_ (fun s => ?_) (fun y z h => ?_)
  · rw [algebraMap_sq_algebraMap, Ext.algebraMap_eq]
    exact isUnit_mk (IsLocalization.Away.algebraMap_isUnit (S := Rg) g) 0
  · obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj (S := Rg) g s.fst
    obtain ⟨m, b, hm⟩ := IsLocalization.Away.surj (S := Rg) g s.snd
    refine ⟨n + m, Ext.mk (zeroDatum R) (a * g ^ m) (b * g ^ n), ?_⟩
    rw [algebraMap_sq_algebraMap_pow]
    ext
    · simp only [fst_mul, Ext.fst_mk, fst_algebraMap_sq, map_mul, map_pow]
      linear_combination (algebraMap R Rg g ^ m) * hn
    · simp only [snd_mul, Ext.fst_mk, Ext.snd_mk, snd_algebraMap_sq, smul_eq_mul, mul_zero,
        zero_add, map_mul, map_pow]
      linear_combination (algebraMap R Rg g ^ n) * hm
  · have h1 : algebraMap R Rg y.fst = algebraMap R Rg z.fst := by
      simpa using congrArg Ext.fst h
    have h2 : algebraMap R Rg y.snd = algebraMap R Rg z.snd := by
      simpa using congrArg Ext.snd h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := Rg) g h1
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (S := Rg) g h2
    refine ⟨n + m, ?_⟩
    rw [algebraMap_pow_eq]
    ext
    · simp only [fst_mul, Ext.fst_mk]
      linear_combination (g ^ m) * hn
    · simp only [snd_mul, Ext.fst_mk, Ext.snd_mk, smul_eq_mul, mul_zero, add_zero]
      linear_combination (g ^ n) * hm

/-! ### The morphism of spectra -/

/-- `Spec (Sq R) ⟶ Spec R` is an integral morphism. -/
instance isIntegralHom_specMap_algebraMap (R : CommRingCat.{u}) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R (Sq R)))) := by
  rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom]
  exact algebraMap_isIntegral_iff.mpr inferInstance

/-- `Spec (Sq R) ⟶ Spec R` is surjective. -/
theorem surjective_specMap_algebraMap (R : CommRingCat.{u}) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap R (Sq R)))) := by
  rw [surjective_iff]
  show Function.Surjective (PrimeSpectrum.comap (algebraMap (R : Type u) (Sq R)))
  intro P
  obtain ⟨Q, hQ, hQ'⟩ :=
    Ext.exists_isPrime_comap_eq (d := zeroDatum (R : Type u)) P.asIdeal
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQ'⟩

end

end Stacks.SqZero

end
