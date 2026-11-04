module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Spectrum

/-!
# Extension of scalars of the algebra of a free algebra structure

Let `m` be a free `d`-dimensional algebra structure over a commutative ring `R` and let
`φ : R →+* S` be a ring homomorphism. Extending the scalars of the structure constants gives the
free `d`-dimensional structure `m.map φ` over `S`, and applying `φ` to each coordinate is a ring
homomorphism `Carrier m ⟶ Carrier (m.map φ)` compatible with the two unit maps. The resulting
square of rings is a pushout: both horizontal edges are free on the `d` standard basis vectors,
and the lower one expands the images of the upper one.

Consequently the square of spectra is cartesian: the spectrum of the algebra of `m.map φ` is the
base change along `Spec φ` of the spectrum of the algebra of `m`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.Carrier.mapRingHom`: the coordinatewise extension of
  scalars `Carrier m →+* Carrier (m.map φ)`.
* `AlgebraicGeometry.FiniteFreeAlgebra.specCoverBaseChangeIso`: the spectrum of the algebra of
  `m.map φ` as the base change of the spectrum of the algebra of `m`, as an isomorphism of
  schemes over `Spec S`.

## Main results

* `AlgebraicGeometry.isPushout_of_bases_one`: a commuting square of commutative rings whose two
  horizontal edges carry bases indexed by one type, the lower expanding the images of the upper,
  is a pushout.
* `AlgebraicGeometry.FiniteFreeAlgebra.isPushout_carrier_map`: the square of rings attached to
  `φ` and `m` is a pushout.
* `AlgebraicGeometry.FiniteFreeAlgebra.isPullback_specCover_map`: the square of spectra is
  cartesian.

## Implementation notes

The two algebra structures that the pushout statement needs are the ones `φ` and the unit map of
`Carrier m` determine, so they are introduced as `RingHom.toAlgebra` instances inside the proof
rather than assumed; the statement itself is about ring homomorphisms only, which is the form in
which the base change of a cover arrives.

That the square of spectra is cartesian is Mathlib's
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout` applied to it.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **A commuting square of commutative rings whose two horizontal edges carry bases indexed by
the same type, the lower one expanding the images of the upper one, is a pushout square.** -/
theorem isPushout_of_bases_one {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B] {ι : Type*} [Fintype ι]
    (bU : Module.Basis ι R S) (b : Module.Basis ι A B)
    (h : ∀ x : S, algebraMap S B x = ∑ i, algebraMap R A (bU.repr x i) • b i) :
    Algebra.IsPushout R S A B := by
  refine Algebra.IsPushout.symm ?_
  rw [Algebra.isPushout_iff]
  refine IsBaseChange.of_equiv ((bU.baseChange A).equiv b (Equiv.refl ι)) fun x => ?_
  have hbase : ∀ i : ι, ((bU.baseChange A).equiv b (Equiv.refl ι)) (1 ⊗ₜ[R] bU i) = b i := by
    intro i
    have h1 : (1 : A) ⊗ₜ[R] bU i = (bU.baseChange A) i :=
      (Module.Basis.baseChange_apply (S := A) bU i).symm
    rw [h1, Module.Basis.equiv_apply, Equiv.refl_apply]
  change ((bU.baseChange A).equiv b (Equiv.refl ι)) (1 ⊗ₜ[R] x) = algebraMap S B x
  rw [h x]
  conv_lhs => rw [← bU.sum_repr x]
  rw [TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.tmul_smul, ← algebraMap_smul A (bU.repr x i), map_smul, hbase i]

namespace FiniteFreeAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]

namespace Carrier

/-- Applying a ring homomorphism to each coordinate, as a map from the algebra of a free
`d`-dimensional structure to the algebra of the structure with extended scalars. -/
def mapFun (φ : R →+* S) (m : FiniteFreeAlgebra R d) (x : Carrier m) : Carrier (m.map φ) :=
  (fun k => φ (x k) : Fin d → S)

/-- The `k`th coordinate of `mapFun φ m x` is `φ` applied to the `k`th coordinate of `x`. -/
@[simp] theorem mapFun_apply (φ : R →+* S) (m : FiniteFreeAlgebra R d) (x : Carrier m)
    (k : Fin d) : mapFun φ m x k = φ (x k) := rfl

/-- Applying a ring homomorphism to each coordinate is a ring homomorphism from the algebra of a
free `d`-dimensional structure to the algebra of the structure with extended scalars. -/
def mapRingHom (φ : R →+* S) (m : FiniteFreeAlgebra R d) :
    Carrier m →+* Carrier (m.map φ) where
  toFun := mapFun φ m
  map_one' := ext fun k => by
    rw [mapFun_apply, one_apply, one_apply]
    split <;> simp
  map_mul' x y := ext fun k => by
    rw [mapFun_apply, mul_apply, mul_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, mapFun_apply, mapFun_apply]
    rfl
  map_zero' := ext fun k => by
    rw [mapFun_apply, zero_apply, zero_apply, map_zero]
  map_add' x y := ext fun k => by
    rw [mapFun_apply, add_apply, add_apply, map_add, mapFun_apply, mapFun_apply]

/-- The `k`th coordinate of `mapRingHom φ m x` is `φ` applied to the `k`th coordinate of `x`. -/
@[simp] theorem mapRingHom_apply (φ : R →+* S) (m : FiniteFreeAlgebra R d) (x : Carrier m)
    (k : Fin d) : mapRingHom φ m x k = φ (x k) := rfl

/-- The coordinatewise extension of scalars carries the `i`th standard basis vector to the `i`th
standard basis vector. -/
theorem mapRingHom_basisVector (φ : R →+* S) (m : FiniteFreeAlgebra R d) (i : Fin d) :
    mapRingHom φ m (basisVector m i) = basisVector (m.map φ) i :=
  ext fun k => by simp [apply_ite φ]

/-- The coordinatewise extension of scalars is compatible with the two unit maps. -/
theorem mapRingHom_comp_algebraMap (φ : R →+* S) (m : FiniteFreeAlgebra R d) :
    (mapRingHom φ m).comp (algebraMap R (Carrier m)) =
      (algebraMap S (Carrier (m.map φ))).comp φ :=
  RingHom.ext fun r => ext fun k => by simp [apply_ite φ]

end Carrier

open Carrier

/-- **The algebra of a free `d`-dimensional structure with extended scalars is the base change of
the algebra of the structure.** The square formed by the unit maps of the two algebras, the given
ring homomorphism and the coordinatewise extension of scalars is a pushout of commutative
rings. -/
theorem isPushout_carrier_map (φ : R →+* S) (m : FiniteFreeAlgebra R d) :
    IsPushout (ofHom (algebraMap R (Carrier m))) (ofHom φ)
      (ofHom (Carrier.mapRingHom φ m)) (ofHom (algebraMap S (Carrier (m.map φ)))) := by
  let : Algebra R S := φ.toAlgebra
  let : Algebra (Carrier m) (Carrier (m.map φ)) := (Carrier.mapRingHom φ m).toAlgebra
  let : Algebra R (Carrier (m.map φ)) :=
    ((algebraMap S (Carrier (m.map φ))).comp φ).toAlgebra
  have : IsScalarTower R S (Carrier (m.map φ)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R (Carrier m) (Carrier (m.map φ)) :=
    IsScalarTower.of_algebraMap_eq' (Carrier.mapRingHom_comp_algebraMap φ m).symm
  have : Algebra.IsPushout R (Carrier m) S (Carrier (m.map φ)) := by
    refine isPushout_of_bases_one (Carrier.basis m) (Carrier.basis (m.map φ)) fun x => ?_
    change Carrier.mapRingHom φ m x = _
    refine ext fun k => ?_
    have hterm : ∀ i : Fin d,
        (algebraMap R S ((Carrier.basis m).repr x i) • Carrier.basis (m.map φ) i) k =
          φ (x i) * (if k = i then (1 : S) else 0) := by
      intro i
      rw [Carrier.smul_apply, basis_apply, basisVector_apply]
      rfl
    rw [mapRingHom_apply, Carrier.sum_apply, Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_eq_single k (fun i _ hi => by simp [Ne.symm hi])
        (fun h => absurd (Finset.mem_univ k) h)]
    simp
  exact CommRingCat.isPushout_of_isPushout R (Carrier m) S (Carrier (m.map φ))

/-- **The spectrum of the algebra of a free `d`-dimensional structure with extended scalars is
the base change of the spectrum of the algebra of the structure.** -/
theorem isPullback_specCover_map (φ : R →+* S) (m : FiniteFreeAlgebra R d) :
    IsPullback (Spec.map (ofHom (Carrier.mapRingHom φ m)))
      (Spec.map (ofHom (algebraMap S (Carrier (m.map φ)))))
      (Spec.map (ofHom (algebraMap R (Carrier m)))) (Spec.map (ofHom φ)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_carrier_map φ m)

/-- The spectrum of the algebra of `m.map φ`, as the base change along `Spec φ` of the spectrum
of the algebra of `m`: an isomorphism of schemes over `Spec S`. -/
noncomputable def specCoverBaseChangeIso (φ : R →+* S) (m : FiniteFreeAlgebra R d) :
    (Over.pullback (Spec.map (ofHom φ))).obj (specCover m) ≅ specCover (m.map φ) :=
  Over.isoMk (isPullback_specCover_map φ m).isoPullback.symm
    (IsPullback.isoPullback_inv_snd (isPullback_specCover_map φ m))

end FiniteFreeAlgebra

end AlgebraicGeometry

end
