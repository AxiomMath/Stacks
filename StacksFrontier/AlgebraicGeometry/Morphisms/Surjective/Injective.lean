module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksCore.Tactic.StacksAttribute

/-!
# Injectivity on points is not stable under base change

The inclusion `ℝ → ℂ` induces a bijection `Spec ℂ ⟶ Spec ℝ` on points, both spectra being
single points. Its base change along itself is the projection from `Spec (ℂ ⊗[ℝ] ℂ)`, and the
tensor square splits as `ℂ × ℂ`, so that spectrum has two points. The base-changed morphism
therefore maps two points to one and is not injective. Consequently neither injectivity nor
bijectivity of the underlying point map is stable under base change for morphisms of schemes.

## Main definitions

* `AlgebraicGeometry.complexSpecMap` is the morphism `Spec ℂ ⟶ Spec ℝ`.
* `AlgebraicGeometry.complexTensorSpecMap` is the projection from `Spec (ℂ ⊗[ℝ] ℂ)` to
  `Spec ℂ`.

## Main results

* `AlgebraicGeometry.complexSpecMap_bijective` gives bijectivity before base change.
* `AlgebraicGeometry.complexTensorSpec_isPullback` identifies the explicit tensor-square square
  as a pullback.
* `AlgebraicGeometry.complexTensor_ringEquiv_prod` gives the product decomposition, including
  its idempotent.
* `AlgebraicGeometry.complexTensorSpec_two_points` counts the points of the pullback.
* `AlgebraicGeometry.complexTensorSpecMap_not_injective` gives the failure of injectivity after
  base change.
* `AlgebraicGeometry.injective_not_stableUnderBaseChange` and
  `AlgebraicGeometry.bijective_not_stableUnderBaseChange` state the two resulting failures of
  stability.

## References

* [Stacks Project, Tag 0496](https://stacks.math.columbia.edu/tag/0496)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A map to a subsingleton out of a two-element type is not injective. -/
private theorem not_injective_of_card_two {α β : Type*} [Subsingleton β]
    (f : α → β) (h : Nat.card α = 2) : ¬ Function.Injective f := by
  intro hf
  have : Subsingleton α := hf.subsingleton
  have : Finite α := Nat.finite_of_card_ne_zero (by omega : Nat.card α ≠ 0)
  have := Finite.card_le_one_iff_subsingleton.mpr (inferInstance : Subsingleton α)
  omega

/-- The splitting of the tensor square of `ℂ` over `ℝ`, sending `z ⊗ w` to
`(conj z * w, z * w)`. -/
private noncomputable def complexTensorSplitHom :
    ℂ ⊗[ℝ] ℂ →ₐ[ℂ] ℂ × ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ (ℂ × ℂ))
    (Complex.conjAe.toAlgHom.prod (AlgHom.id ℝ ℂ))
    fun _ _ => Commute.all _ _

/-- The splitting is injective: in the basis `1 ⊗ 1`, `1 ⊗ i` its matrix is invertible. -/
private theorem complexTensorSplitHom_injective :
    Function.Injective complexTensorSplitHom := by
  let b := Algebra.TensorProduct.basis ℂ Complex.basisOneI
  intro x y h
  have hx : complexTensorSplitHom (x - y) = 0 := by
    rw [map_sub, h, sub_self]
  let c₀ := b.repr (x - y) 0
  let c₁ := b.repr (x - y) 1
  have hrepr : x - y = c₀ • b 0 + c₁ • b 1 := by
    simpa [c₀, c₁] using (b.sum_repr (x - y)).symm
  have hb₀ : complexTensorSplitHom (b 0) = (1, 1) := by
    simp [b, complexTensorSplitHom]
  have hb₁ : complexTensorSplitHom (b 1) = (-Complex.I, Complex.I) := by
    simp [b, complexTensorSplitHom]
  have hcoords : complexTensorSplitHom (x - y) =
      (c₀ - c₁ * Complex.I, c₀ + c₁ * Complex.I) := by
    rw [hrepr, map_add, map_smul, map_smul, hb₀, hb₁]
    ext <;> (simp; try ring_nf)
  have hh : (c₀ - c₁ * Complex.I, c₀ + c₁ * Complex.I) = (0, 0) :=
    hcoords.symm.trans hx
  have h₀ := congrArg Prod.fst hh
  have h₁ := congrArg Prod.snd hh
  have hc₀ : c₀ = 0 := by linear_combination (h₀ + h₁) / 2
  have hc₁I : c₁ * Complex.I = 0 := by linear_combination (h₁ - h₀) / 2
  have hc₁ : c₁ = 0 := (mul_eq_zero.mp hc₁I).resolve_right Complex.I_ne_zero
  have hxy : x - y = 0 := by rw [hrepr]; simp [hc₀, hc₁]
  exact sub_eq_zero.mp hxy

/-- The tensor square of `ℂ` over `ℝ` is isomorphic to `ℂ × ℂ` as a `ℂ`-algebra. -/
private noncomputable def complexTensorSplitEquiv :
    ℂ ⊗[ℝ] ℂ ≃ₐ[ℂ] ℂ × ℂ :=
  AlgEquiv.ofBijective complexTensorSplitHom
    ⟨complexTensorSplitHom_injective, fun ⟨z, w⟩ => by
      let a : ℂ := (z + w) / 2
      let b : ℂ := (w - z) / (2 * Complex.I)
      refine ⟨a • (1 ⊗ₜ[ℝ] (1 : ℂ)) + b • (1 ⊗ₜ[ℝ] Complex.I), ?_⟩
      simp [complexTensorSplitHom, a, b]
      field_simp
      ring_nf
      trivial⟩

/-- A scheme `Spec R` with `R ≃+* ℂ × ℂ` has exactly two points. -/
private theorem card_spec_eq_two_of_ringEquiv {R : Type*} [CommRing R] (e : R ≃+* ℂ × ℂ) :
    Nat.card (Spec (.of R)) = 2 := by
  change Nat.card (PrimeSpectrum R) = 2
  rw [Nat.card_congr ((PrimeSpectrum.comapEquiv e).toEquiv.trans
    (PrimeSpectrum.primeSpectrumProd ℂ ℂ))]
  simp

/-- A ring map between rings with one-point nonempty spectra is bijective on spectra. -/
private theorem bijective_comap_of_subsingleton {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Subsingleton (PrimeSpectrum R)] [Subsingleton (PrimeSpectrum S)]
    (x : PrimeSpectrum S) : Function.Bijective (PrimeSpectrum.comap (algebraMap R S)) :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨x, Subsingleton.elim _ _⟩⟩

section

attribute [local instance] ULift.algebra'

universe u

/-- The universe-polymorphic form of `complexSpecMap`. -/
private noncomputable def liftedComplexSpecMap :
    Spec (.of (ULift.{u} ℂ)) ⟶ Spec (.of (ULift.{u} ℝ)) :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℝ) (ULift.{u} ℂ))).op

/-- The universe-polymorphic form of `complexTensorSpecMap`. -/
private noncomputable def liftedComplexTensorSpecMap :
    Spec (.of (ULift.{u} ℂ ⊗[ULift.{u} ℝ] ULift.{u} ℂ)) ⟶
      Spec (.of (ULift.{u} ℂ)) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : ULift.{u} ℂ →ₐ[ULift.{u} ℝ]
      ULift.{u} ℂ ⊗[ULift.{u} ℝ] ULift.{u} ℂ).toRingHom).op

/-- The spectrum of a lifted field is a single point. -/
private theorem uliftPrimeSpectrum_subsingleton {R : Type*} [Field R] :
    Subsingleton (PrimeSpectrum (ULift.{u} R)) :=
  ⟨fun _ _ => (PrimeSpectrum.comapEquiv (ULift.ringEquiv : ULift.{u} R ≃+* R)).injective
    (Subsingleton.elim _ _)⟩

/-- The lifted morphism is bijective on points. -/
private theorem liftedComplexSpecMap_bijective :
    Function.Bijective (liftedComplexSpecMap.{u}).base := by
  have := uliftPrimeSpectrum_subsingleton.{u} (R := ℝ)
  have := uliftPrimeSpectrum_subsingleton.{u} (R := ℂ)
  exact bijective_comap_of_subsingleton
    ((PrimeSpectrum.comapEquiv (ULift.ringEquiv : ULift.{u} ℂ ≃+* ℂ)).symm default)

/-- The lifted tensor-square square is a pullback. -/
private theorem liftedComplexTensorSpec_isPullback :
    IsPullback
      (Scheme.Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeft : ULift.{u} ℂ →ₐ[ULift.{u} ℝ]
          ULift.{u} ℂ ⊗[ULift.{u} ℝ] ULift.{u} ℂ).toRingHom)).op)
      (liftedComplexTensorSpecMap.{u})
      (liftedComplexSpecMap.{u}) (liftedComplexSpecMap.{u}) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (ULift.{u} ℝ) (ULift.{u} ℂ) (ULift.{u} ℂ))

/-- The lifted tensor square is isomorphic to `ℂ × ℂ` as a ring. -/
private noncomputable def liftedTensorRingEquiv :
    (ULift.{u} ℂ ⊗[ULift.{u} ℝ] ULift.{u} ℂ) ≃+* (ℂ × ℂ) :=
  (Algebra.TensorProduct.uliftEquiv.{u, u, u, u} ℝ ℝ ℂ ℂ).symm.toRingEquiv.trans
    (ULift.ringEquiv.trans complexTensorSplitEquiv.toRingEquiv)

/-- The lifted tensor square has a two-point spectrum. -/
private theorem liftedComplexTensorSpec_two_points :
    Nat.card (Spec (.of (ULift.{u} ℂ ⊗[ULift.{u} ℝ] ULift.{u} ℂ))) = 2 := by
  exact card_spec_eq_two_of_ringEquiv liftedTensorRingEquiv.{u}

/-- The lifted base-changed morphism is not injective on points. -/
private theorem liftedComplexTensorSpecMap_not_injective :
    ¬ Function.Injective (liftedComplexTensorSpecMap.{u}).base := by
  have : Subsingleton (Spec (.of (ULift.{u} ℂ))) := by
    change Subsingleton (PrimeSpectrum (ULift.{u} ℂ))
    exact uliftPrimeSpectrum_subsingleton
  exact not_injective_of_card_two _ liftedComplexTensorSpec_two_points

end

/-- The map on spectra induced by the inclusion of the reals into the complexes. -/
public noncomputable abbrev complexSpecMap : Spec (.of ℂ) ⟶ Spec (.of ℝ) :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)).op

/-- The projection from the spectrum of the tensor square induced by its right factor. -/
public noncomputable abbrev complexTensorSpecMap :
    Spec (.of (ℂ ⊗[ℝ] ℂ)) ⟶ Spec (.of ℂ) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] ℂ).toRingHom).op

/-- `Spec ℂ ⟶ Spec ℝ` is a bijection on points. -/
@[stacks 0496 "bijectivity before base change"]
public theorem complexSpecMap_bijective : Function.Bijective complexSpecMap.base := by
  exact bijective_comap_of_subsingleton (R := ℝ) default

/-- The tensor-square spectrum realizes the base change of `Spec ℂ ⟶ Spec ℝ`
along itself. -/
@[stacks 0496 "the base-change square"]
public theorem complexTensorSpec_isPullback :
    IsPullback
      (Scheme.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] ℂ).toRingHom).op)
      complexTensorSpecMap complexSpecMap complexSpecMap :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct ℝ ℂ ℂ)

/-- The tensor square of `ℂ` over `ℝ` splits into two copies of `ℂ`, with the
indicated idempotent selecting the first factor. -/
@[stacks 0496 "product decomposition and idempotent"]
public theorem complexTensor_ringEquiv_prod :
    ∃ e : (ℂ ⊗[ℝ] ℂ) ≃+* (ℂ × ℂ),
      e ((1 / 2 : ℝ) • (1 + Complex.I ⊗ₜ[ℝ] Complex.I)) = (1, 0) := by
  refine ⟨complexTensorSplitEquiv.toRingEquiv, ?_⟩
  unfold complexTensorSplitEquiv
  change (complexTensorSplitHom.restrictScalars ℝ)
    ((1 / 2 : ℝ) • (1 + Complex.I ⊗ₜ[ℝ] Complex.I)) = (1, 0)
  rw [map_smul]
  ext <;> norm_num [complexTensorSplitHom]

/-- The spectrum of the tensor square has exactly two points. -/
@[stacks 0496 "two points after base change"]
public theorem complexTensorSpec_two_points :
    Nat.card (Spec (.of (ℂ ⊗[ℝ] ℂ))) = 2 := by
  exact card_spec_eq_two_of_ringEquiv complexTensorSplitEquiv.toRingEquiv

/-- The base-changed map is not injective on points. -/
@[stacks 0496 "noninjectivity after base change"]
public theorem complexTensorSpecMap_not_injective :
    ¬ Function.Injective complexTensorSpecMap.base := by
  have : Subsingleton (Spec (.of ℂ)) := inferInstance
  exact not_injective_of_card_two _ complexTensorSpec_two_points

/-- Injectivity of the underlying point map is not stable under base change
for scheme morphisms. -/
@[stacks 0496 "injectivity is not stable"]
public theorem injective_not_stableUnderBaseChange :
    ¬ CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      (P := fun ⦃X Y : Scheme⦄ (f : X ⟶ Y) => Function.Injective f.base) := by
  intro hstable
  exact liftedComplexTensorSpecMap_not_injective
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃X Y : Scheme⦄ (f : X ⟶ Y) => Function.Injective f.base)
      liftedComplexTensorSpec_isPullback liftedComplexSpecMap_bijective.1)

/-- Bijectivity of the underlying point map is not stable under base change
for scheme morphisms. -/
@[stacks 0496 "bijectivity is not stable"]
public theorem bijective_not_stableUnderBaseChange :
    ¬ CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      (P := fun ⦃X Y : Scheme⦄ (f : X ⟶ Y) => Function.Bijective f.base) := by
  intro hstable
  apply liftedComplexTensorSpecMap_not_injective
  exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃X Y : Scheme⦄ (f : X ⟶ Y) => Function.Bijective f.base)
    liftedComplexTensorSpec_isPullback liftedComplexSpecMap_bijective).1

end AlgebraicGeometry
