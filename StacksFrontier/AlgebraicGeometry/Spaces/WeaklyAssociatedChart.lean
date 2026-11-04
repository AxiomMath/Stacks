module

public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.RingEquiv

/-!
# Weak association read on an étale chart

Let `X` be an algebraic space over `S`, let `F` be an `𝒪_X`-module and let `x̄` be a geometric
point of `X`. The geometric stalk `F_{x̄}` is formed as the stalk of `F` at the point of the
small étale site determined by `x̄`, with its scalars extended along the comparison of that
stalk's ring with the étale local ring `𝒪_{X, x̄}`. The comparison is a ring isomorphism, so
extension of scalars along it changes neither elements nor annihilators, and weak association of
the maximal ideal may therefore be read off the stalk indexed by the étale charts of `x̄`,
before the extension.

## Main results

* `isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv`: weak association of the maximal
  ideal transports along a semilinear isomorphism of modules over isomorphic local rings.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_moduleStalkLarge`: a point is weakly
  associated to a module exactly when, at some geometric point above it, the maximal ideal of
  the stalk of the structure sheaf at the corresponding point of the small étale site is weakly
  associated to the stalk of the module there.

## References

* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u m

/-! ### Scalar extension along a ring isomorphism -/

namespace IsLocalRing

/-- The maximal ideal of a local ring is the contraction of the maximal ideal of an isomorphic
local ring. -/
theorem comap_ringEquiv_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) :
    Ideal.comap (e : R →+* S) (maximalIdeal S) = maximalIdeal R := by
  ext r
  simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  refine not_congr ⟨fun h => ?_, fun h => h.map (e : R →+* S)⟩
  simpa only [RingHom.coe_coe, RingEquiv.symm_apply_apply] using h.map (e.symm : S →+* R)

end IsLocalRing

/-- Extension of scalars along a ring isomorphism, as an additive isomorphism of the underlying
groups: an element is sent to its tensor with `1`. -/
noncomputable def ModuleCat.extendScalarsRingEquivAddEquiv {R T : Type*} [CommRing R]
    [CommRing T] (e : R ≃+* T) (M : ModuleCat R) :
    M ≃+ (ModuleCat.extendScalars e.toRingHom).obj M := by
  letI : Algebra R T := e.toRingHom.toAlgebra
  exact ((TensorProduct.congr (Module.compHom.toLinearEquiv e).symm
    (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)).toAddEquiv.symm

/-- The scalar extension isomorphism along a ring isomorphism sends `x` to `1 ⊗ x`. -/
theorem ModuleCat.extendScalarsRingEquivAddEquiv_apply {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (M : ModuleCat R) (x : M) :
    ModuleCat.extendScalarsRingEquivAddEquiv e M x = (1 : T) ⊗ₜ[R, e.toRingHom] x := by
  let : Algebra R T := e.toRingHom.toAlgebra
  show (TensorProduct.congr (Module.compHom.toLinearEquiv e)
    (LinearEquiv.refl R M)) ((TensorProduct.lid R M).symm x) = _
  simp
  rfl

/-- The scalar extension isomorphism along a ring isomorphism is semilinear along it. -/
theorem ModuleCat.extendScalarsRingEquivAddEquiv_smul {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (M : ModuleCat R) (r : R) (x : M) :
    ModuleCat.extendScalarsRingEquivAddEquiv e M (r • x) =
      e r • ModuleCat.extendScalarsRingEquivAddEquiv e M x := by
  let : Algebra R T := e.toRingHom.toAlgebra
  rw [ModuleCat.extendScalarsRingEquivAddEquiv_apply,
    ModuleCat.extendScalarsRingEquivAddEquiv_apply]
  show (1 : T) ⊗ₜ[R] (r • x) = e r • ((1 : T) ⊗ₜ[R] x)
  rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul (R := R) r (1 : T) x]
  congr 1

/-! ### Weak association across a semilinear isomorphism -/

/-- Contraction of ideals along a ring isomorphism is injective. -/
private theorem Ideal.comap_ringEquiv_injective {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Function.Injective (Ideal.comap (e : R →+* S)) := by
  intro I J h
  ext s
  simpa only [Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply] using
    Ideal.ext_iff.mp h (e.symm s)

/-- Weak association of the maximal ideal of the target pulls back along a semilinear additive
isomorphism over a ring isomorphism of local rings. -/
private theorem isWeaklyAssociatedPrime_maximalIdeal_of_semilinearEquiv {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module S N] (e : R ≃+* S) (φ : M ≃+ N)
    (hφ : ∀ (r : R) (x : M), φ (r • x) = e r • φ x)
    (h : IsWeaklyAssociatedPrime S N (IsLocalRing.maximalIdeal S)) :
    IsWeaklyAssociatedPrime R M (IsLocalRing.maximalIdeal R) := by
  obtain ⟨I, hI, hIeq⟩ := weaklyAssociatedPrimes_subset_comap_image_of_semilinearEquiv e φ hφ h
  exact Ideal.comap_ringEquiv_injective e.symm
    (hIeq.trans (IsLocalRing.comap_ringEquiv_maximalIdeal e.symm).symm) ▸ hI

/-- Weak association of the maximal ideal transports along an additive isomorphism of modules
over isomorphic local rings which is semilinear along the ring isomorphism. -/
theorem isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (e : R ≃+* S) (φ : M ≃+ N)
    (hφ : ∀ (r : R) (x : M), φ (r • x) = e r • φ x) :
    IsWeaklyAssociatedPrime R M (IsLocalRing.maximalIdeal R) ↔
      IsWeaklyAssociatedPrime S N (IsLocalRing.maximalIdeal S) :=
  ⟨isWeaklyAssociatedPrime_maximalIdeal_of_semilinearEquiv e.symm φ.symm fun s y => by
      apply φ.injective
      rw [φ.apply_symm_apply, hφ, e.apply_symm_apply, φ.apply_symm_apply],
    isWeaklyAssociatedPrime_maximalIdeal_of_semilinearEquiv e φ hφ⟩

namespace AlgebraicGeometry.Space

/-- **Stacks 0CTX**, weak association read before the extension of scalars: a point of an
algebraic space is weakly associated to an `𝒪_X`-module exactly when, at some geometric point
above it, the maximal ideal of the stalk of the structure sheaf at the corresponding point of
the small étale site is weakly associated to the stalk of the module there. -/
@[stacks 0CTX "weak association on the stalk at the point of the small étale site"]
theorem isWeaklyAssociatedPoint_iff_moduleStalkLarge (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2)
    (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X F x ↔
      ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
        letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
          isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
        letI : IsLocalRing
            (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
              (smallEtaleRingedTopos B S hS X).O.obj) :=
          (pointStalkRingEquiv B S hS X xbar).symm.isLocalRing
        IsWeaklyAssociatedPrime
          (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
            (smallEtaleRingedTopos B S hS X).O.obj)
          (Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 xbar X.2)
            (smallEtaleRingedTopos B S hS X).O F)
          (IsLocalRing.maximalIdeal _) := by
  refine exists_congr fun xbar => and_congr_right fun _ => ?_
  let : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  let : IsLocalRing
      (((etaleSitePoint B S hS X.1 xbar X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj) :=
    (pointStalkRingEquiv B S hS X xbar).symm.isLocalRing
  exact (isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv
    (pointStalkRingEquiv B S hS X xbar)
    (ModuleCat.extendScalarsRingEquivAddEquiv (pointStalkRingEquiv B S hS X xbar) _)
    (ModuleCat.extendScalarsRingEquivAddEquiv_smul _ _)).symm

end AlgebraicGeometry.Space

end
