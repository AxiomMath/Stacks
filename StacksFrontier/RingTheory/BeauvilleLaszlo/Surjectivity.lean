module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Covering
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueingPair

/-!
# Detecting surjectivity of an algebra map over a glueing pair

For a glueing pair `(R → R', f)` the `R`-module `R' ⊕ R_f` is faithful, so a property of an
`R`-module which is detected by vanishing can be checked after the two base changes
`- ⊗ R'` and `- ⊗ R_f`. Applied to the cokernel of an algebra map this says that an
`R`-algebra homomorphism is surjective as soon as it becomes surjective after localizing away
from `f` and after extending scalars to `R'`.

## Main definitions

* `BeauvilleLaszlo.IsGlueingPair`: a ring map `φ : R → R'` together with `f : R` is a
  *glueing pair* when `φ` induces an isomorphism `R/fⁿR → R'/fⁿR'` for every `n > 0` and the
  Beauville--Laszlo sequence `0 → R → R' ⊕ R_f → R'_f → 0` is short exact.

## Main results

* `BeauvilleLaszlo.surjective_of_baseChange_and_awayMap_surjective`: surjectivity of an
  `R`-algebra homomorphism is detected by its two base changes along a glueing pair.

## Implementation notes

The two components of `BeauvilleLaszlo.IsGlueingPair` are stated through the objects the rest
of this directory already uses: `BeauvilleLaszlo.quotientPowMap`, which carries the
isomorphism condition as bijectivity of a concrete ring map rather than as an abstract
isomorphism, and `BeauvilleLaszlo.beauvilleLaszloSequence`, whose short exactness is the
remaining half of the definition. By
`BeauvilleLaszlo.beauvilleLaszloSequence_exactness_iff_powerTorsionMap` the second component
is equivalent to bijectivity of the map on `f`-power torsion.

The localized base change is presented by the canonical map between localizations away from
the images of `f`, and the other base change by the canonical map of tensor products. Only the
isomorphism component of the glueing-pair hypothesis is used in the proof, through
`BeauvilleLaszlo.tensorProduct_prod_away_nontrivial_of_quotientMap_bijective`, which is stated
for `Ideal.quotientMap` of the ideal power rather than for `quotientPowMap`; the two are
identified by `Ideal.map_pow` and `Ideal.map_span`.

## References

* [Stacks Project, Tag 0BNH](https://stacks.math.columbia.edu/tag/0BNH)
* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
-/

universe u v w x

@[expose] public section

namespace BeauvilleLaszlo

open scoped TensorProduct

/-- A ring map `φ : R → R'` and an element `f : R` form a **glueing pair** when `φ` induces an
isomorphism `R/fⁿR → R'/fⁿR'` for every `n > 0` and the Beauville--Laszlo sequence
`0 → R → R' ⊕ R_f → R'_f → 0` is short exact. -/
def IsGlueingPair {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    (φ : R →+* R') (f : R) : Prop :=
  (∀ n : ℕ, 0 < n → Function.Bijective (quotientPowMap f n φ)) ∧
    (beauvilleLaszloSequence f φ).ShortExact

/-- The cokernel of a linear map whose base change along `M ↦ M ⊗ T` is surjective has
vanishing base change along `M ↦ M ⊗ T`. -/
private theorem tensor_cokernel_subsingleton_of_map_surjective
    {R : Type*} [CommRing R] {M N T : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T]
    [Module R M] [Module R N] [Module R T]
    (g : M →ₗ[R] N)
    (hg : Function.Surjective
      (TensorProduct.AlgebraTensorModule.map g (LinearMap.id (R := R) (M := T)))) :
    Subsingleton ((N ⧸ LinearMap.range g) ⊗[R] T) := by
  have hc : (LinearMap.range g).mkQ.comp g = 0 := by
    ext m
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range g)).mpr ⟨m, rfl⟩
  have hzero (x : (N ⧸ LinearMap.range g) ⊗[R] T) : x = 0 := by
    obtain ⟨y, hy⟩ := TensorProduct.map_surjective
      (LinearMap.range g).mkQ_surjective
      (show Function.Surjective (LinearMap.id (R := R) (M := T)) from fun t => ⟨t, rfl⟩) x
    have hmaps : TensorProduct.AlgebraTensorModule.map (LinearMap.range g).mkQ
        (LinearMap.id (R := R) (M := T)) =
        TensorProduct.map (LinearMap.range g).mkQ LinearMap.id := by
      ext
      rfl
    rw [← hy, ← hmaps]
    obtain ⟨z, rfl⟩ := hg y
    change ((TensorProduct.AlgebraTensorModule.map (LinearMap.range g).mkQ LinearMap.id).comp
      (TensorProduct.AlgebraTensorModule.map g LinearMap.id)) z = 0
    rw [← TensorProduct.AlgebraTensorModule.map_comp, hc]
    have hz : TensorProduct.AlgebraTensorModule.map
        (0 : M →ₗ[R] (N ⧸ LinearMap.range g))
        (LinearMap.id (R := R) (M := T)) = 0 := by
      ext
      simp
    rw [LinearMap.id_comp, hz]
    rfl
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- An `R`-algebra homomorphism is surjective if it becomes surjective both after localization
away from `f` and after extension of scalars to `R'`, where `(R → R', f)` is a glueing pair. -/
lemma surjective_of_baseChange_and_awayMap_surjective
    {R : Type u} {R' : Type v} {A : Type w} {B : Type x}
    [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
    [Algebra R R'] [Algebra R A] [Algebra R B]
    (f : R) (hglue : IsGlueingPair (algebraMap R R') f) (φ : A →ₐ[R] B)
    (haway : Function.Surjective (Localization.awayMap φ.toRingHom (algebraMap R A f)))
    (hbase : Function.Surjective (Algebra.TensorProduct.map φ (AlgHom.id R R'))) :
    Function.Surjective φ := by
  let g : A →ₗ[R] B := φ.toLinearMap
  have hbase' : Function.Surjective
      (TensorProduct.AlgebraTensorModule.map g (LinearMap.id (R := R) (M := R'))) :=
    fun x ↦ hbase x
  let eA : A ⊗[R] Localization.Away f ≃ₐ[A] Localization.Away (algebraMap R A f) :=
    IsLocalization.Away.tensorEquiv A f (Localization.Away f)
  have : IsLocalization.Away (φ (algebraMap R A f)) (B ⊗[R] Localization.Away f) := by
    rw [φ.commutes f]
    infer_instance
  let eB : B ⊗[R] Localization.Away f ≃ₐ[B] Localization.Away (φ (algebraMap R A f)) :=
    IsLocalization.algEquiv (Submonoid.powers (φ (algebraMap R A f))) _ _
  have hsquare : eB.toRingHom.comp
        (Algebra.TensorProduct.map φ (AlgHom.id R (Localization.Away f))).toRingHom =
      (Localization.awayMap φ.toRingHom (algebraMap R A f)).comp eA.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A f))
    ext a
    change eB (φ a ⊗ₜ[R] (1 : Localization.Away f)) =
      Localization.awayMap φ.toRingHom (algebraMap R A f)
        (eA (a ⊗ₜ[R] (1 : Localization.Away f)))
    calc
      eB (φ a ⊗ₜ[R] (1 : Localization.Away f)) = algebraMap B _ (φ a) := eB.commutes (φ a)
      _ = Localization.awayMap φ.toRingHom (algebraMap R A f) (algebraMap A _ a) := by
            simp [Localization.awayMap, IsLocalization.Away.map]
      _ = Localization.awayMap φ.toRingHom (algebraMap R A f)
            (eA (a ⊗ₜ[R] (1 : Localization.Away f))) := by
            simpa using congrArg
              (Localization.awayMap φ.toRingHom (algebraMap R A f)) (eA.commutes a).symm
  have haway' : Function.Surjective
      (TensorProduct.AlgebraTensorModule.map g
        (LinearMap.id (R := R) (M := Localization.Away f))) := by
    intro z
    obtain ⟨y, hy⟩ := haway (eB z)
    obtain ⟨t, rfl⟩ := eA.surjective y
    refine ⟨t, ?_⟩
    apply eB.injective
    rw [← hy]
    exact DFunLike.congr_fun hsquare t
  let N := B ⧸ LinearMap.range g
  have : Subsingleton (N ⊗[R] R') :=
    tensor_cokernel_subsingleton_of_map_surjective g hbase'
  have : Subsingleton (N ⊗[R] Localization.Away f) :=
    tensor_cokernel_subsingleton_of_map_surjective g haway'
  have : Subsingleton (R' ⊗[R] N) :=
    Equiv.subsingleton (TensorProduct.comm R R' N).toEquiv
  have : Subsingleton (Localization.Away f ⊗[R] N) :=
    Equiv.subsingleton (TensorProduct.comm R (Localization.Away f) N).toEquiv
  have : Subsingleton ((R' × Localization.Away f) ⊗[R] N) :=
    (TensorProduct.prodLeft R R R' (Localization.Away f) N).injective.subsingleton
  have : Subsingleton (N ⊗[R] (R' × Localization.Away f)) :=
    Equiv.subsingleton (TensorProduct.comm R N (R' × Localization.Away f)).toEquiv
  -- The faithfulness statement is phrased for `Ideal.quotientMap` of the ideal power, which
  -- is `quotientPowMap` up to the identification of `(span {f}) ^ n` with its image.
  have hquot : ∀ n : ℕ, 0 < n → Function.Bijective
      (Ideal.quotientMap (Ideal.map (algebraMap R R') ((Ideal.span {f}) ^ n))
        (algebraMap R R') Ideal.le_comap_map) := by
    intro n hn
    have hideal : Ideal.map (algebraMap R R') ((Ideal.span {f}) ^ n) =
        (Ideal.span {algebraMap R R' f}) ^ n := by
      rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    let e := Ideal.quotEquivOfEq hideal
    let q := Ideal.quotientMap (Ideal.map (algebraMap R R') ((Ideal.span {f}) ^ n))
      (algebraMap R R') Ideal.le_comap_map
    have heq : e.toRingHom.comp q = quotientPowMap f n (algebraMap R R') := by
      ext r
      exact Ideal.quotEquivOfEq_mk hideal (algebraMap R R' r)
    apply (e.bijective.of_comp_iff' q).mp
    change Function.Bijective (e.toRingHom.comp q)
    rw [heq]
    exact hglue.1 n hn
  have : Subsingleton N := by
    by_contra hN
    have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN
    exact not_nontrivial _
      ((tensorProduct_prod_away_nontrivial_of_quotientMap_bijective R f).1 R' hquot N)
  intro b
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range g)).mp
    (Subsingleton.elim (Submodule.Quotient.mk (p := LinearMap.range g) b) 0)
  exact ⟨a, ha⟩

end BeauvilleLaszlo

end
