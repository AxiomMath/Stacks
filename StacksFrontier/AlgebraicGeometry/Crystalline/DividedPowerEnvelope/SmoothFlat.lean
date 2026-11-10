module

public import Mathlib.RingTheory.RingHom.Bijective
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.BaseChangeHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.SmoothLocalCoordinates

/-!
# Flatness and base change of divided power envelopes of smooth presentations

Let `(A, I, γ)` be a divided power ring with `p` nilpotent in `A`, let `A → B` be a ring map and
`J ⊆ B` an ideal containing `I B`, and let `D = D_{B,γ}(J)` be its divided power envelope.

The main results are for a *smooth presentation*: `B` smooth over `A` and `π : B → C` surjective
with `C` smooth over `A ⧸ I` and `J = ker π`.

* `Crystalline.flat_structureMap_dividedPowerEnvelope_of_smooth` — `D_{B,γ}(J)` is flat over `A`;
* `Crystalline.bijective_envelopeBaseChangeHom_of_smooth` and
  `Crystalline.envelopeBaseChangeEquivOfSmooth` — for every homomorphism of divided power rings
  `φ : (A, I, γ) → (A₁, I₁, γ₁)` the canonical map
  `A₁ ⊗_A D_{B,γ}(J) → D_{A₁ ⊗_A B, γ₁}(J (A₁ ⊗_A B) + I₁ (A₁ ⊗_A B))` is an isomorphism;
* `Crystalline.ker_tensorQuotientMap` — that ideal is the kernel of the base-changed presentation
  `A₁ ⊗_A B → (A₁ ⧸ I₁) ⊗_{A ⧸ I} C`, whence
  `Crystalline.bijective_envelopeBaseChangeHom_of_smooth_ker`.

Neither `A` Noetherian nor `A` a `ℤ_(p)`-algebra is needed. A smooth presentation has local flat
coordinates by `Crystalline.exists_localizationAway_flat_mvPolynomial_of_smooth`, and the results
are deduced from the following general ones.

Suppose that near every point of `V(J)` the ideal `J` is cut out, together with `I`, by part of
a flat coordinate system: there is `g` with `J B_g = I B_g + (t_1, …, t_c)` and `B_g` flat over
`A[x_1, …, x_c]` along `x_i ↦ t_i` (`Crystalline.HasLocalFlatCoordinates`). Then

* `D` is flat over `A` (`Crystalline.flat_structureMap_of_hasLocalFlatCoordinates`);
* for every homomorphism of divided power rings `(A, I, γ) → (A₁, I₁, γ₁)` the canonical map
  `A₁ ⊗_A D → D_{A₁ ⊗_A B, γ₁}(J (A₁ ⊗_A B) + I₁ (A₁ ⊗_A B))` is bijective
  (`Crystalline.bijective_envelopeBaseChangeHom_of_hasLocalFlatCoordinates`).

The proof is the one of the hints to [Stacks, Tag 07MU]. On `B_g` the envelope is
`B_g ⊗_{A[x]} A⟨x⟩` by flat base change (Stacks 07HD), which is flat over `A` and commutes with
base change because `A⟨x⟩` does. Both properties are local on `D`: the elements `g` together
with the elements of `J` generate the unit ideal of `B`, the elements of `J` become nilpotent in
`D` because `p` is nilpotent, and the envelope of `J B_g` is the localization of `D` at `g`.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 07HD](https://stacks.math.columbia.edu/tag/07HD)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Crystalline

open DividedPowers

section Localization

/-- Viewing `T` as an `S`-algebra through an `R`-algebra map `f : S → T` gives a scalar tower. -/
private theorem isScalarTower_toAlgebra {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    letI := f.toRingHom.toAlgebra
    IsScalarTower R S T := by
  let := f.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (f.commutes a).symm)

/-- `S ⊗_R B'` is the localization at `1 ⊗ g` when `B'` is the localization of `B` at `g`. -/
private theorem isLocalization_away_tmul_tensor {R S B : Type*} [CommRing R] [CommRing S]
    [CommRing B] [Algebra R S] [Algebra R B] (g : B) (B' : Type*) [CommRing B'] [Algebra R B']
    [Algebra B B'] [IsScalarTower R B B'] [IsLocalization.Away g B']
    [Algebra (S ⊗[R] B) (S ⊗[R] B')] [IsScalarTower S (S ⊗[R] B) (S ⊗[R] B')]
    (H : (algebraMap (S ⊗[R] B) (S ⊗[R] B')).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap B B')) :
    IsLocalization.Away ((1 : S) ⊗ₜ[R] g) (S ⊗[R] B') := by
  simpa only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using
    IsLocalization.tensorProduct_tensorProduct_right R S (Submonoid.powers g) B' H

variable {A A₁ : DividedPowerRing.{u}} [Algebra A A₁]
  (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
  (hφ : φ.toRingHom = algebraMap A A₁)
  {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] [Algebra B B']
  [IsScalarTower A B B'] (g : B) [IsLocalization.Away g B']
  {J : Ideal B} {hJ : A.ideal.map (algebraMap A B) ≤ J}
  {J' : Ideal B'} {hJ' : A.ideal.map (algebraMap A B') ≤ J'}
  (hJ'eq : J' = J.map (algebraMap B B'))
  (D : DividedPowerEnvelope A (algebraMap A B) J hJ)
  (D' : DividedPowerEnvelope A (algebraMap A B') J' hJ')

include hJ'eq in
/-- The envelope over `B_g` is the localization away from `g` of the envelope over `B`. -/
theorem isLocalization_away_envelopeMapOfAlgebra :
    letI : Algebra D.object D'.object := (envelopeMapOfAlgebra hJ'eq.ge D D').toRingHom.toAlgebra
    IsLocalization.Away (D.algebraMap.toRingHom g) D'.object :=
  isLocalization_away_envelopeAlgebraMapHom g D D' (IsScalarTower.algebraMap_eq A B B') hJ'eq

include hJ'eq in
/-- `A₁ ⊗_A D_{B_g}` is the localization away from `1 ⊗ g` of `A₁ ⊗_A D_B`. -/
theorem isLocalization_away_tensorEnvelopeMap :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    letI : Algebra A D'.object := D'.structureMap.toRingHom.toAlgebra
    letI : Algebra (A₁ ⊗[A] D.object) (A₁ ⊗[A] D'.object) :=
      (tensorEnvelopeMap hJ'eq.ge D D').toRingHom.toAlgebra
    IsLocalization.Away ((1 : A₁) ⊗ₜ[A] D.algebraMap.toRingHom g) (A₁ ⊗[A] D'.object) := by
  let : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
  let : Algebra A D'.object := D'.structureMap.toRingHom.toAlgebra
  let : Algebra D.object D'.object := (envelopeMapOfAlgebra hJ'eq.ge D D').toRingHom.toAlgebra
  have : IsScalarTower A D.object D'.object := IsScalarTower.of_algebraMap_eq' (by
    ext z
    exact (envelopeAlgebraMapHom_structureMap D D' _ hJ'eq.ge z).symm)
  have := isLocalization_away_envelopeMapOfAlgebra g hJ'eq D D'
  let : Algebra (A₁ ⊗[A] D.object) (A₁ ⊗[A] D'.object) :=
    (tensorEnvelopeMap hJ'eq.ge D D').toRingHom.toAlgebra
  have : IsScalarTower A₁ (A₁ ⊗[A] D.object) (A₁ ⊗[A] D'.object) :=
    isScalarTower_toAlgebra (tensorEnvelopeMap hJ'eq.ge D D')
  exact isLocalization_away_tmul_tensor (S := A₁) (D.algebraMap.toRingHom g) D'.object (by
    ext d
    rfl)

variable {J₁ : Ideal (A₁ ⊗[A] B)} {hJ₁ : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤ J₁}
  {J₁' : Ideal (A₁ ⊗[A] B')} {hJ₁' : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B')) ≤ J₁'}
  (hJ₁'eq : J₁' = J₁.map (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B')).toRingHom)
  (D₁ : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B)) J₁ hJ₁)
  (D₁' : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B')) J₁' hJ₁')

include hJ₁'eq in
/-- The envelope over `A₁ ⊗_A B_g` is the localization away from `1 ⊗ g` of the envelope over
`A₁ ⊗_A B`. -/
theorem isLocalization_away_envelopeMapOfTensor :
    letI : Algebra D₁.object D₁'.object :=
      (envelopeMapOfTensor hJ₁'eq.ge D₁ D₁').toRingHom.toAlgebra
    IsLocalization.Away (D₁.algebraMap.toRingHom ((1 : A₁) ⊗ₜ[A] g)) D₁'.object := by
  let : Algebra (A₁ ⊗[A] B) (A₁ ⊗[A] B') :=
    (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B')).toRingHom.toAlgebra
  have : IsScalarTower A₁ (A₁ ⊗[A] B) (A₁ ⊗[A] B') :=
    isScalarTower_toAlgebra (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := B'))
  have : IsLocalization.Away ((1 : A₁) ⊗ₜ[A] g) (A₁ ⊗[A] B') :=
    isLocalization_away_tmul_tensor (S := A₁) g B' (by
      ext b
      rfl)
  exact isLocalization_away_envelopeAlgebraMapHom ((1 : A₁) ⊗ₜ[A] g) D₁ D₁'
    (tensorAlgebraMap_comp_algebraMap (A₁ := A₁) (B := B) (B' := B')).symm hJ₁'eq

end Localization

section Coordinates

variable {A : DividedPowerRing.{u}} {B' : Type u} [CommRing B'] [Algebra A B'] {W : Type u}
  (t : W → B')
  (ht : (MvPolynomial.aeval t : MvPolynomial W A →ₐ[A] B').toRingHom.Flat)
  {J' : Ideal B'} (hJ'eq : J' = A.ideal.map (algebraMap A B') ⊔ Ideal.span (Set.range t))
  {hJ' : A.ideal.map (algebraMap A B') ≤ J'}
  (D' : DividedPowerEnvelope A (algebraMap A B') J' hJ')

include hJ'eq in
/-- The ideal `I B' + (t)` is the extension of `I A[x] + (x)` along `x ↦ t`. -/
theorem map_polynomialModelIdeal_aeval :
    letI : Algebra (MvPolynomial W A) B' := (MvPolynomial.aeval t).toRingHom.toAlgebra
    J' = (polynomialModelIdeal A (MvPolynomial.X : W → MvPolynomial W A)).map
      (algebraMap (MvPolynomial W A) B') := by
  let : Algebra (MvPolynomial W A) B' := (MvPolynomial.aeval t).toRingHom.toAlgebra
  rw [hJ'eq, polynomialModelIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span]
  congr 1
  · congr 1
    ext a
    exact ((MvPolynomial.aeval t).commutes a).symm
  · congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, MvPolynomial.aeval_X t i⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (MvPolynomial.aeval_X t i).symm⟩

include ht hJ'eq in
/-- **An envelope cut out by part of a flat coordinate system is flat over the base.** -/
theorem flat_structureMap_of_coordinates : D'.structureMap.toRingHom.Flat := by
  let : Algebra (MvPolynomial W A) B' := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial W A) B' := isScalarTower_toAlgebra (MvPolynomial.aeval t)
  have : Module.Flat (MvPolynomial W A) B' := ht
  set E := polynomialModelEnvelopeX (A := A) W
  obtain ⟨e, he⟩ := exists_envelope_tensor_equiv_of_flat E D'
    (IsScalarTower.algebraMap_eq A (MvPolynomial W A) B')
    (map_polynomialModelIdeal_aeval t hJ'eq)
  let : Algebra (MvPolynomial W A) E.object := E.algebraMap.toRingHom.toAlgebra
  have hstruct : D'.structureMap.toRingHom = e.toRingHom.comp
      ((algebraMap E.object (E.object ⊗[MvPolynomial W A] B')).comp
        E.structureMap.toRingHom) := by
    ext a
    change D'.structureMap.toRingHom a = e (E.structureMap.toRingHom a ⊗ₜ 1)
    rw [he, map_one, mul_one, envelopeAlgebraMapHom_structureMap]
  rw [hstruct]
  exact RingHom.Flat.comp (RingHom.Flat.comp (flat_structureMap_polynomialModelEnvelope A _ _)
    (RingHom.flat_algebraMap_iff.mpr inferInstance)) (RingHom.Flat.of_bijective e.bijective)

variable {A₁ : DividedPowerRing.{u}} [Algebra A A₁]
  (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
  (hφ : φ.toRingHom = algebraMap A A₁)

include hφ in
/-- The extension of `I` to `A₁ ⊗_A B` lies in the extension of `I₁`. -/
theorem map_includeRight_map_algebraMap_le {B : Type u} [CommRing B] [Algebra A B] :
    (A.ideal.map (algebraMap A B)).map
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ≤
      A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) := by
  rw [Ideal.map_map, includeRight_comp_algebraMap_eq φ hφ, ← Ideal.map_map]
  exact Ideal.map_mono φ.ideal_comp

include hφ hJ'eq in
/-- The ideal of `A₁ ⊗_A B'` generated by `J'` and `I₁` is the extension of
`I₁ (A₁ ⊗_A A[x]) + (1 ⊗ x)` along `x ↦ t`. -/
theorem map_polynomialModelIdeal_tensor_aeval {J₁' : Ideal (A₁ ⊗[A] B')}
    (hJ₁'eq : J₁' = J'.map (Algebra.TensorProduct.includeRight : B' →ₐ[A] A₁ ⊗[A] B').toRingHom ⊔
      A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B'))) :
    letI : Algebra (MvPolynomial W A) B' := (MvPolynomial.aeval t).toRingHom.toAlgebra
    haveI : IsScalarTower A (MvPolynomial W A) B' := IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact ((MvPolynomial.aeval t).commutes a).symm)
    J₁' = (polynomialModelIdeal A₁ (fun w => (1 : A₁) ⊗ₜ[A] (MvPolynomial.X w :
        MvPolynomial W A))).map
      (tensorAlgebraMap (A₁ := A₁) (B := MvPolynomial W A) (B' := B')).toRingHom := by
  let : Algebra (MvPolynomial W A) B' := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial W A) B' := isScalarTower_toAlgebra (MvPolynomial.aeval t)
  have hspan : Ideal.span ((tensorAlgebraMap (A₁ := A₁) (B := MvPolynomial W A)
      (B' := B')).toRingHom '' Set.range (fun w => (1 : A₁) ⊗ₜ[A] (MvPolynomial.X w :
        MvPolynomial W A))) =
      Ideal.span ((Algebra.TensorProduct.includeRight : B' →ₐ[A] A₁ ⊗[A] B').toRingHom ''
        Set.range t) := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 2
    funext w
    change (1 : A₁) ⊗ₜ[A] (MvPolynomial.aeval t (MvPolynomial.X w)) = (1 : A₁) ⊗ₜ[A] t w
    rw [MvPolynomial.aeval_X]
  rw [hJ₁'eq, hJ'eq, polynomialModelIdeal, Ideal.map_sup, Ideal.map_sup,
    Ideal.map_span, Ideal.map_span, hspan,
    Ideal.map_map (algebraMap A₁ (A₁ ⊗[A] MvPolynomial W A)),
    tensorAlgebraMap_comp_algebraMap (A₁ := A₁) (B := MvPolynomial W A) (B' := B')]
  apply le_antisymm
  · refine sup_le (sup_le ?_ le_sup_right) le_sup_left
    exact (map_includeRight_map_algebraMap_le φ hφ).trans le_sup_left
  · exact sup_le le_sup_right (le_sup_of_le_left le_sup_right)

include ht hφ hJ'eq in
/-- **The base change map of an envelope cut out by part of a flat coordinate system is
bijective.** -/
theorem bijective_envelopeBaseChangeHom_of_coordinates {J₁' : Ideal (A₁ ⊗[A] B')}
    {hJ₁' : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B')) ≤ J₁'}
    (hJ₁'eq : J₁' = J'.map (Algebra.TensorProduct.includeRight : B' →ₐ[A] A₁ ⊗[A] B').toRingHom ⊔
      A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B')))
    (hJ'J₁' : J'.map (Algebra.TensorProduct.includeRight : B' →ₐ[A] A₁ ⊗[A] B').toRingHom ≤ J₁')
    (D₁' : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B')) J₁' hJ₁') :
    Function.Bijective (envelopeBaseChangeHom φ hφ hJ'J₁' D' D₁') := by
  let : Algebra (MvPolynomial W A) B' := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial W A) B' := isScalarTower_toAlgebra (MvPolynomial.aeval t)
  have : Module.Flat (MvPolynomial W A) B' := ht
  exact bijective_envelopeBaseChangeHom_of_flat φ hφ (map_polynomialModelIdeal_X_le φ hφ W)
    hJ'J₁' (polynomialModelEnvelopeX W) D' (polynomialModelEnvelopeTensorX (A₁ := A₁) W) D₁'
    (map_polynomialModelIdeal_aeval t hJ'eq)
    (map_polynomialModelIdeal_tensor_aeval t hJ'eq φ hφ hJ₁'eq)
    (bijective_envelopeBaseChangeHom_model φ hφ W)

end Coordinates

end Crystalline

namespace Crystalline

open DividedPowers

section Assembly

variable {A : DividedPowerRing.{u}} {B : Type u} [CommRing B] [Algebra A B]

/-- Near every point of `V(J)`, the ideal `J` is cut out, together with the divided power ideal
of the base, by part of a flat coordinate system. -/
def HasLocalFlatCoordinates (J : Ideal B) : Prop :=
  ∀ q : Ideal B, q.IsMaximal → J ≤ q → ∃ g : B, g ∉ q ∧ ∃ (c : ℕ)
    (t : Fin c → Localization.Away g),
    (MvPolynomial.aeval t : MvPolynomial (Fin c) A →ₐ[A] Localization.Away g).toRingHom.Flat ∧
    J.map (algebraMap B (Localization.Away g)) =
      A.ideal.map (algebraMap A (Localization.Away g)) ⊔ Ideal.span (Set.range t)

/-- The elements `g` at which `J` is cut out by part of a flat coordinate system. -/
def flatCoordinateElements (J : Ideal B) : Set B :=
  {g | ∃ (c : ℕ) (t : Fin c → Localization.Away g),
    (MvPolynomial.aeval t : MvPolynomial (Fin c) A →ₐ[A] Localization.Away g).toRingHom.Flat ∧
    J.map (algebraMap B (Localization.Away g)) =
      A.ideal.map (algebraMap A (Localization.Away g)) ⊔ Ideal.span (Set.range t)}

/-- The elements with local flat coordinates together with `J` generate the unit ideal. -/
theorem span_flatCoordinateElements_union_eq_top {J : Ideal B}
    (hloc : HasLocalFlatCoordinates (A := A) J) :
    Ideal.span (flatCoordinateElements (A := A) J ∪ (J : Set B)) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  by_cases hJm : J ≤ m
  · obtain ⟨g, hg, hgood⟩ := hloc m hm hJm
    exact hg (hle (Ideal.subset_span (Or.inl hgood)))
  · obtain ⟨j, hj, hjm⟩ := Set.not_subset.mp hJm
    exact hjm (hle (Ideal.subset_span (Or.inr hj)))

/-- Reindexing a flat coordinate system along `ULift.down` keeps it flat and keeps its range. -/
theorem exists_ulift_coordinates {B' : Type u} [CommRing B'] [Algebra A B'] {c : ℕ}
    (t : Fin c → B')
    (ht : (MvPolynomial.aeval t : MvPolynomial (Fin c) A →ₐ[A] B').toRingHom.Flat) :
    (MvPolynomial.aeval (t ∘ ULift.down) :
        MvPolynomial (ULift.{u} (Fin c)) A →ₐ[A] B').toRingHom.Flat ∧
      Set.range (t ∘ ULift.down) = Set.range t := by
  refine ⟨?_, ULift.down_surjective.range_comp t⟩
  have h : (MvPolynomial.aeval (t ∘ ULift.down) :
      MvPolynomial (ULift.{u} (Fin c)) A →ₐ[A] B').toRingHom =
      (MvPolynomial.aeval t : MvPolynomial (Fin c) A →ₐ[A] B').toRingHom.comp
        (MvPolynomial.renameEquiv A Equiv.ulift).toRingEquiv.toRingHom := by
    ext p <;> simp [MvPolynomial.renameEquiv]
  rw [h]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (AlgEquiv.bijective _)) ht

/-- The extension of `I` to `B_g` lies in the extension of `J`. -/
theorem map_algebraMap_localization_le {J : Ideal B} (hJ : A.ideal.map (algebraMap A B) ≤ J)
    (g : B) : A.ideal.map (algebraMap A (Localization.Away g)) ≤
      J.map (algebraMap B (Localization.Away g)) := by
  rw [IsScalarTower.algebraMap_eq A B (Localization.Away g), ← Ideal.map_map]
  exact Ideal.map_mono hJ

/-- **Flatness of a divided power envelope with local flat coordinates.** -/
theorem flat_structureMap_of_hasLocalFlatCoordinates {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A)) {J : Ideal B} (hJ : A.ideal.map (algebraMap A B) ≤ J)
    (hloc : HasLocalFlatCoordinates (A := A) J)
    (D : DividedPowerEnvelope A (algebraMap A B) J hJ) : D.structureMap.toRingHom.Flat := by
  refine RingHom.OfLocalizationSpanTarget.ofIsLocalization
    RingHom.Flat.ofLocalizationSpanTarget RingHom.Flat.respectsIso D.structureMap.toRingHom
    (D.algebraMap.toRingHom '' (flatCoordinateElements (A := A) J ∪ (J : Set B)))
    (by rw [← Ideal.map_span, span_flatCoordinateElements_union_eq_top hloc, Ideal.map_top]) ?_
  rintro ⟨_, g, hg, rfl⟩
  rcases hg with ⟨c, t, ht, htJ⟩ | hgJ
  · let D' := dividedPowerEnvelope A (algebraMap A (Localization.Away g))
      (J.map (algebraMap B (Localization.Away g))) (map_algebraMap_localization_le hJ g)
    let : Algebra D.object D'.object := (envelopeMapOfAlgebra le_rfl D D').toRingHom.toAlgebra
    refine ⟨D'.object, inferInstance, inferInstance,
      isLocalization_away_envelopeMapOfAlgebra g rfl D D', ?_⟩
    have hstruct : (algebraMap D.object D'.object).comp D.structureMap.toRingHom =
        D'.structureMap.toRingHom := by
      ext z
      exact envelopeAlgebraMapHom_structureMap D D' _ le_rfl z
    rw [hstruct]
    obtain ⟨ht', hrange⟩ := exists_ulift_coordinates t ht
    exact flat_structureMap_of_coordinates (t ∘ ULift.down) ht' (by rwa [hrange]) D'
  · obtain ⟨n, hn⟩ := isNilpotent_envelope_algebraMap_of_mem hp hpA D hgJ
    refine ⟨Localization.Away (D.algebraMap.toRingHom g), inferInstance, inferInstance,
      inferInstance, ?_⟩
    have : Subsingleton (Localization.Away (D.algebraMap.toRingHom g)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (D.algebraMap.toRingHom g))
        ⟨n, hn⟩
    let := ((algebraMap D.object (Localization.Away (D.algebraMap.toRingHom g))).comp
      D.structureMap.toRingHom).toAlgebra
    exact Module.Flat.of_free

variable {A₁ : DividedPowerRing.{u}} [Algebra A A₁]
  (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
  (hφ : φ.toRingHom = algebraMap A A₁)

/-- The ideal `J₁` commutes with localization away from `g`. -/
theorem map_tensorAlgebraMap_localization {J : Ideal B} {J₁ : Ideal (A₁ ⊗[A] B)}
    (hJ₁eq : J₁ = J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
      A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B))) (g : B) :
    (J.map (algebraMap B (Localization.Away g))).map
        (Algebra.TensorProduct.includeRight :
          Localization.Away g →ₐ[A] A₁ ⊗[A] Localization.Away g).toRingHom ⊔
      A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] Localization.Away g)) =
    J₁.map (tensorAlgebraMap (A₁ := A₁) (B := B) (B' := Localization.Away g)).toRingHom := by
  rw [hJ₁eq, Ideal.map_sup, Ideal.map_map, Ideal.map_map, Ideal.map_map,
    tensorAlgebraMap_comp_algebraMap (A₁ := A₁) (B := B) (B' := Localization.Away g)]
  congr 2

include hφ in
/-- **Bijectivity of the base change map of an envelope with local flat coordinates.** -/
theorem bijective_envelopeBaseChangeHom_of_hasLocalFlatCoordinates {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A)) {J : Ideal B} (hJ : A.ideal.map (algebraMap A B) ≤ J)
    (hloc : HasLocalFlatCoordinates (A := A) J)
    {J₁ : Ideal (A₁ ⊗[A] B)} {hJ₁ : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤ J₁}
    (hJ₁eq : J₁ = J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
      A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)))
    (hJJ₁ : J.map (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ≤ J₁)
    (D : DividedPowerEnvelope A (algebraMap A B) J hJ)
    (D₁ : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B)) J₁ hJ₁) :
    Function.Bijective (envelopeBaseChangeHom φ hφ hJJ₁ D D₁) := by
  let : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
  let ι : B →+* A₁ ⊗[A] D.object :=
    (Algebra.TensorProduct.includeRight : D.object →ₐ[A] A₁ ⊗[A] D.object).toRingHom.comp
      D.algebraMap.toRingHom
  refine RingHom.OfLocalizationSpan.ofIsLocalization RingHom.Bijective.ofLocalizationSpan
    RingHom.Bijective.respectsIso (envelopeBaseChangeHom φ hφ hJJ₁ D D₁)
    (ι '' (flatCoordinateElements (A := A) J ∪ (J : Set B)))
    (by rw [← Ideal.map_span, span_flatCoordinateElements_union_eq_top hloc, Ideal.map_top]) ?_
  rintro ⟨_, g, hg, rfl⟩
  rcases hg with ⟨c, t, ht, htJ⟩ | hgJ
  · let D' := dividedPowerEnvelope A (algebraMap A (Localization.Away g))
      (J.map (algebraMap B (Localization.Away g))) (map_algebraMap_localization_le hJ g)
    let J₁' : Ideal (A₁ ⊗[A] Localization.Away g) :=
      (J.map (algebraMap B (Localization.Away g))).map
        (Algebra.TensorProduct.includeRight :
          Localization.Away g →ₐ[A] A₁ ⊗[A] Localization.Away g).toRingHom ⊔
      A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] Localization.Away g))
    let D₁' := dividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] Localization.Away g)) J₁'
      le_sup_right
    have hJ₁'eq := map_tensorAlgebraMap_localization hJ₁eq g
    let : Algebra A D'.object := D'.structureMap.toRingHom.toAlgebra
    let : Algebra (A₁ ⊗[A] D.object) (A₁ ⊗[A] D'.object) :=
      (tensorEnvelopeMap le_rfl D D').toRingHom.toAlgebra
    let : Algebra D₁.object D₁'.object :=
      (envelopeMapOfTensor hJ₁'eq.ge D₁ D₁').toRingHom.toAlgebra
    have hΦg : envelopeBaseChangeHom φ hφ hJJ₁ D D₁ (ι g) =
        D₁.algebraMap.toRingHom ((1 : A₁) ⊗ₜ[A] g) :=
      envelopeBaseChangeHom_tmul_algebraMap φ hφ hJJ₁ D D₁ 1 g
    refine ⟨A₁ ⊗[A] D'.object, D₁'.object, inferInstance, inferInstance, inferInstance,
      inferInstance, isLocalization_away_tensorEnvelopeMap g rfl D D',
      by rw [hΦg]; exact isLocalization_away_envelopeMapOfTensor g hJ₁'eq D₁ D₁',
      envelopeBaseChangeHom φ hφ le_sup_left D' D₁', ?_, ?_⟩
    · exact RingHom.ext fun z => envelopeBaseChangeHom_comp_tensorEnvelopeMap φ hφ le_rfl hJJ₁
        le_sup_left hJ₁'eq.ge D D' D₁ D₁' z
    · obtain ⟨ht', hrange⟩ := exists_ulift_coordinates t ht
      exact bijective_envelopeBaseChangeHom_of_coordinates (t ∘ ULift.down) ht'
        (by rwa [hrange]) D' φ hφ rfl le_sup_left D₁'
  · have hnil₁ : IsNilpotent (ι g) := (isNilpotent_envelope_algebraMap_of_mem hp hpA D hgJ).map
      (Algebra.TensorProduct.includeRight : D.object →ₐ[A] A₁ ⊗[A] D.object).toRingHom
    have hnil₂ : IsNilpotent (envelopeBaseChangeHom φ hφ hJJ₁ D D₁ (ι g)) := hnil₁.map _
    obtain ⟨n, hn⟩ := hnil₁
    obtain ⟨m, hm⟩ := hnil₂
    have : Subsingleton (Localization.Away (ι g)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (ι g)) ⟨n, hn⟩
    have : Subsingleton (Localization.Away (envelopeBaseChangeHom φ hφ hJJ₁ D D₁ (ι g))) :=
      IsLocalization.subsingleton (M := Submonoid.powers _) ⟨m, hm⟩
    refine ⟨Localization.Away (ι g),
      Localization.Away (envelopeBaseChangeHom φ hφ hJJ₁ D D₁ (ι g)), inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      IsLocalization.Away.map _ _ (envelopeBaseChangeHom φ hφ hJJ₁ D D₁) (ι g),
      IsLocalization.map_comp _, ?_⟩
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end Assembly

section Smooth

variable {A : DividedPowerRing.{u}} {B C : Type u} [CommRing B] [CommRing C] [Algebra A B]
  [Algebra A C] [Algebra (A ⧸ A.ideal) C] [IsScalarTower A (A ⧸ A.ideal) C]
  [Algebra.Smooth A B] [Algebra.Smooth (A ⧸ A.ideal) C]
  (π : B →ₐ[A] C) (hπ : Function.Surjective π)

include hπ in
/-- The kernel of a surjection from a smooth `A`-algebra onto a smooth `A ⧸ I`-algebra has local
flat coordinates. -/
theorem hasLocalFlatCoordinates_ker_of_smooth :
    HasLocalFlatCoordinates (A := A) (RingHom.ker π.toRingHom) :=
  fun q _ hq => exists_localizationAway_flat_mvPolynomial_of_smooth A.ideal π hπ q hq

omit [Algebra.Smooth A B] [Algebra.Smooth (A ⧸ A.ideal) C] in
/-- The kernel of `π` contains `I B`. -/
theorem map_le_ker_of_smooth :
    A.ideal.map (algebraMap A B) ≤ RingHom.ker π.toRingHom :=
  map_le_ker_of_quotient A.ideal π

include hπ in
/-- **The divided power envelope of a smooth presentation is flat** (the flatness assertion in
the hints to [Stacks, Tag 07MU]). Let `(A, I, γ)` be a divided power ring with `p` nilpotent in
`A`, let `B` be a smooth `A`-algebra and `π : B → C` a surjection onto a smooth `A ⧸ I`-algebra.
Then the divided power envelope `D_{B,γ}(ker π)` is flat over `A`. -/
theorem flat_structureMap_dividedPowerEnvelope_of_smooth {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A)) {hJ : A.ideal.map (algebraMap A B) ≤ RingHom.ker π.toRingHom}
    (D : DividedPowerEnvelope A (algebraMap A B) (RingHom.ker π.toRingHom) hJ) :
    D.structureMap.toRingHom.Flat :=
  flat_structureMap_of_hasLocalFlatCoordinates hp hpA hJ
    (hasLocalFlatCoordinates_ker_of_smooth π hπ) D

include hπ in
/-- **The divided power envelope of a smooth presentation commutes with base change** (the base
change assertion in the hints to [Stacks, Tag 07MU]). Let `(A, I, γ)` be a divided power ring
with `p` nilpotent in `A`, let `B` be a smooth `A`-algebra and `π : B → C` a surjection onto a
smooth `A ⧸ I`-algebra with kernel `J`, and let `φ : (A, I, γ) → (A₁, I₁, γ₁)` be a homomorphism
of divided power rings. Then the canonical map
`A₁ ⊗_A D_{B,γ}(J) → D_{A₁ ⊗_A B, γ₁}(J (A₁ ⊗_A B) + I₁ (A₁ ⊗_A B))` is bijective. -/
theorem bijective_envelopeBaseChangeHom_of_smooth {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A)) {hJ : A.ideal.map (algebraMap A B) ≤ RingHom.ker π.toRingHom}
    {A₁ : DividedPowerRing.{u}} [Algebra A A₁]
    (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
    (hφ : φ.toRingHom = algebraMap A A₁)
    {J₁ : Ideal (A₁ ⊗[A] B)} {hJ₁ : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤ J₁}
    (hJ₁eq : J₁ = (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
        A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)))
    (hJJ₁ : (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ≤ J₁)
    (D : DividedPowerEnvelope A (algebraMap A B) (RingHom.ker π.toRingHom) hJ)
    (D₁ : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B)) J₁ hJ₁) :
    Function.Bijective (envelopeBaseChangeHom φ hφ hJJ₁ D D₁) :=
  bijective_envelopeBaseChangeHom_of_hasLocalFlatCoordinates φ hφ hp hpA hJ
    (hasLocalFlatCoordinates_ker_of_smooth π hπ) hJ₁eq hJJ₁ D D₁

include hπ in
/-- **The canonical isomorphism `A₁ ⊗_A D_{B,γ}(J) ≅ D_{A₁ ⊗_A B, γ₁}(J₁)`** of
`Crystalline.bijective_envelopeBaseChangeHom_of_smooth`. -/
noncomputable def envelopeBaseChangeEquivOfSmooth {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A)) {hJ : A.ideal.map (algebraMap A B) ≤ RingHom.ker π.toRingHom}
    {A₁ : DividedPowerRing.{u}} [Algebra A A₁]
    (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
    (hφ : φ.toRingHom = algebraMap A A₁)
    {J₁ : Ideal (A₁ ⊗[A] B)} {hJ₁ : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤ J₁}
    (hJ₁eq : J₁ = (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
        A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)))
    (hJJ₁ : (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ≤ J₁)
    (D : DividedPowerEnvelope A (algebraMap A B) (RingHom.ker π.toRingHom) hJ)
    (D₁ : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B)) J₁ hJ₁) :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    A₁ ⊗[A] D.object ≃+* D₁.object :=
  RingEquiv.ofBijective (envelopeBaseChangeHom φ hφ hJJ₁ D D₁)
    (bijective_envelopeBaseChangeHom_of_smooth π hπ hp hpA φ hφ hJ₁eq hJJ₁ D D₁)

include hπ in
/-- The isomorphism `A₁ ⊗_A D_{B,γ}(J) ≅ D_{A₁ ⊗_A B, γ₁}(J₁)` on a pure tensor: `a ⊗ d ↦ a ψ(d)`,
with `ψ : D_{B,γ}(J) → D_{A₁ ⊗_A B, γ₁}(J₁)` the divided power morphism over `φ`. -/
theorem envelopeBaseChangeEquivOfSmooth_tmul {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A)) {hJ : A.ideal.map (algebraMap A B) ≤ RingHom.ker π.toRingHom}
    {A₁ : DividedPowerRing.{u}} [Algebra A A₁]
    (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
    (hφ : φ.toRingHom = algebraMap A A₁)
    {J₁ : Ideal (A₁ ⊗[A] B)} {hJ₁ : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤ J₁}
    (hJ₁eq : J₁ = (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
        A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)))
    (hJJ₁ : (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ≤ J₁)
    (D : DividedPowerEnvelope A (algebraMap A B) (RingHom.ker π.toRingHom) hJ)
    (D₁ : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B)) J₁ hJ₁) (a : A₁) (d : D.object) :
    letI : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
    envelopeBaseChangeEquivOfSmooth π hπ hp hpA φ hφ hJ₁eq hJJ₁ D D₁ (a ⊗ₜ[A] d) =
      D₁.structureMap.toRingHom a * (envelopeBaseChangePairMap φ hφ hJJ₁ D D₁).toRingHom d :=
  rfl

end Smooth

section Kernel

variable {A A₁ : DividedPowerRing.{u}} [Algebra A A₁]
  {B C : Type u} [CommRing B] [CommRing C] [Algebra A B]
  [Algebra (A ⧸ A.ideal) C] [Algebra A C] [IsScalarTower A (A ⧸ A.ideal) C]
  (π : B →ₐ[A] C) (hle : A.ideal ≤ A₁.ideal.comap (algebraMap A A₁))

/-- The `A ⧸ I`-algebra structure of `A₁ ⧸ I₁` induced by `A → A₁`. -/
noncomputable abbrev quotientAlgebraOfLE : Algebra (A ⧸ A.ideal) (A₁ ⧸ A₁.ideal) :=
  Ideal.Quotient.algebraQuotientOfLEComap hle

/-- The base change `A₁ ⊗_A B → (A₁ ⧸ I₁) ⊗_{A ⧸ I} C` of `π`, `a ⊗ b ↦ ā ⊗ π b`. -/
noncomputable def tensorQuotientMap :
    letI := quotientAlgebraOfLE hle
    A₁ ⊗[A] B →+* (A₁ ⧸ A₁.ideal) ⊗[A ⧸ A.ideal] C :=
  letI := quotientAlgebraOfLE hle
  let f : A₁ →ₐ[A] (A₁ ⧸ A₁.ideal) ⊗[A ⧸ A.ideal] C :=
    { ((Algebra.TensorProduct.includeLeft : (A₁ ⧸ A₁.ideal) →ₐ[A ⧸ A.ideal]
        (A₁ ⧸ A₁.ideal) ⊗[A ⧸ A.ideal] C).toRingHom.comp (Ideal.Quotient.mk A₁.ideal)) with
      commutes' := fun a => by
        change (Ideal.Quotient.mk A₁.ideal (algebraMap A A₁ a)) ⊗ₜ[A ⧸ A.ideal] (1 : C) = _
        rw [Algebra.TensorProduct.algebraMap_apply]
        rfl }
  let g : B →ₐ[A] (A₁ ⧸ A₁.ideal) ⊗[A ⧸ A.ideal] C :=
    { ((Algebra.TensorProduct.includeRight : C →ₐ[A ⧸ A.ideal]
        (A₁ ⧸ A₁.ideal) ⊗[A ⧸ A.ideal] C).toRingHom.comp π.toRingHom) with
      commutes' := fun a => by
        change (1 : A₁ ⧸ A₁.ideal) ⊗ₜ[A ⧸ A.ideal] π (algebraMap A B a) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ A.ideal) C,
          Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
        rfl }
  (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom

/-- The base change of `π` on a pure tensor. -/
theorem tensorQuotientMap_tmul (a : A₁) (b : B) :
    letI := quotientAlgebraOfLE hle
    tensorQuotientMap π hle (a ⊗ₜ[A] b) =
      Ideal.Quotient.mk A₁.ideal a ⊗ₜ[A ⧸ A.ideal] π b := by
  let := quotientAlgebraOfLE hle
  change Ideal.Quotient.mk A₁.ideal a ⊗ₜ[A ⧸ A.ideal] (1 : C) *
    (1 : A₁ ⧸ A₁.ideal) ⊗ₜ[A ⧸ A.ideal] π b = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The kernel of the base change of a surjection `π` lies in
`(ker π)(A₁ ⊗_A B) + I₁ (A₁ ⊗_A B)`. -/
private theorem ker_tensorQuotientMap_le (hπ : Function.Surjective π) :
    letI := quotientAlgebraOfLE hle
    RingHom.ker (tensorQuotientMap π hle) ≤ (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
        A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) := by
  let := quotientAlgebraOfLE hle
  set J₁ := (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
        A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B))
  have hIQ : A.ideal ≤ J₁.comap (algebraMap A (A₁ ⊗[A] B)) := by
    intro a ha
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A A₁ (A₁ ⊗[A] B)]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (hle ha))
  let : Algebra (A ⧸ A.ideal) ((A₁ ⊗[A] B) ⧸ J₁) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIQ
  have : IsScalarTower A (A ⧸ A.ideal) ((A₁ ⊗[A] B) ⧸ J₁) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  let f' : (A₁ ⧸ A₁.ideal) →ₐ[A ⧸ A.ideal] (A₁ ⊗[A] B) ⧸ J₁ :=
    { Ideal.Quotient.lift A₁.ideal ((Ideal.Quotient.mk J₁).comp (algebraMap A₁ (A₁ ⊗[A] B)))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))) with
      commutes' := fun r => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        change Ideal.Quotient.mk J₁ (algebraMap A₁ (A₁ ⊗[A] B) (algebraMap A A₁ a)) =
          Ideal.Quotient.mk J₁ (algebraMap A (A₁ ⊗[A] B) a)
        rw [← IsScalarTower.algebraMap_apply] }
  let g₀ : B →ₐ[A] (A₁ ⊗[A] B) ⧸ J₁ :=
    (Ideal.Quotient.mkₐ A J₁).comp Algebra.TensorProduct.includeRight
  let g₁ : C →ₐ[A] (A₁ ⊗[A] B) ⧸ J₁ := AlgHom.liftOfSurjective π hπ g₀ (fun b hb => by
    change Ideal.Quotient.mk J₁ ((1 : A₁) ⊗ₜ[A] b) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb)))
  let g' : C →ₐ[A ⧸ A.ideal] (A₁ ⊗[A] B) ⧸ J₁ :=
    AlgHom.extendScalarsOfSurjective Ideal.Quotient.mk_surjective g₁
  let inv : (A₁ ⧸ A₁.ideal) ⊗[A ⧸ A.ideal] C →+* (A₁ ⊗[A] B) ⧸ J₁ :=
    (Algebra.TensorProduct.lift f' g' (fun _ _ => Commute.all _ _)).toRingHom
  have key : ∀ x, inv (tensorQuotientMap π hle x) = Ideal.Quotient.mk J₁ x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul a b =>
      rw [tensorQuotientMap_tmul]
      change f' (Ideal.Quotient.mk A₁.ideal a) * g₁ (π b) = _
      rw [AlgHom.liftOfSurjective_apply]
      change Ideal.Quotient.mk J₁ (algebraMap A₁ (A₁ ⊗[A] B) a) *
        Ideal.Quotient.mk J₁ ((1 : A₁) ⊗ₜ[A] b) = _
      rw [← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
      rfl
  intro x hx
  have := key x
  rw [RingHom.mem_ker.mp hx, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm

/-- The ideal `(ker π)(A₁ ⊗_A B) + I₁ (A₁ ⊗_A B)` lies in the kernel of the base change of `π`. -/
private theorem map_sup_le_ker_tensorQuotientMap :
    letI := quotientAlgebraOfLE hle
    (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
        A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤
      RingHom.ker (tensorQuotientMap π hle) := by
  let := quotientAlgebraOfLE hle
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change tensorQuotientMap π hle ((1 : A₁) ⊗ₜ[A] j) = 0
    rw [tensorQuotientMap_tmul]
    change _ ⊗ₜ[A ⧸ A.ideal] π j = 0
    rw [show π j = 0 from hj, TensorProduct.tmul_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, tensorQuotientMap_tmul,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, TensorProduct.zero_tmul]

/-- **The kernel of the base-changed presentation.** For a surjection `π : B → C` of `A`-algebras
onto an `A ⧸ I`-algebra and `A → A₁` carrying `I` into `I₁`, the kernel of
`A₁ ⊗_A B → (A₁ ⧸ I₁) ⊗_{A ⧸ I} C` is `(ker π)(A₁ ⊗_A B) + I₁ (A₁ ⊗_A B)`. -/
theorem ker_tensorQuotientMap (hπ : Function.Surjective π) :
    letI := quotientAlgebraOfLE hle
    RingHom.ker (tensorQuotientMap π hle) = (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ⊔
        A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) := by
  let := quotientAlgebraOfLE hle
  exact le_antisymm (ker_tensorQuotientMap_le π hle hπ) (map_sup_le_ker_tensorQuotientMap π hle)

end Kernel

section SmoothKernel

variable {A : DividedPowerRing.{u}} {B C : Type u} [CommRing B] [CommRing C] [Algebra A B]
  [Algebra A C] [Algebra (A ⧸ A.ideal) C] [IsScalarTower A (A ⧸ A.ideal) C]
  [Algebra.Smooth A B] [Algebra.Smooth (A ⧸ A.ideal) C]
  (π : B →ₐ[A] C) (hπ : Function.Surjective π)

include hπ in
/-- **Base change of the envelope of a smooth presentation, with the base-changed target.**
For a homomorphism of divided power rings `φ : (A, I, γ) → (A₁, I₁, γ₁)`, the canonical map
`A₁ ⊗_A D_{B,γ}(ker π) → D_{A₁ ⊗_A B, γ₁}(ker π₁)` is bijective, where
`π₁ : A₁ ⊗_A B → (A₁ ⧸ I₁) ⊗_{A ⧸ I} C` is the base change of `π`. -/
theorem bijective_envelopeBaseChangeHom_of_smooth_ker {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A)) {hJ : A.ideal.map (algebraMap A B) ≤ RingHom.ker π.toRingHom}
    {A₁ : DividedPowerRing.{u}} [Algebra A A₁]
    (φ : DividedPowers.DPMorphism A.dividedPowers A₁.dividedPowers)
    (hφ : φ.toRingHom = algebraMap A A₁) (hle : A.ideal ≤ A₁.ideal.comap (algebraMap A A₁))
    {hJ₁ : A₁.ideal.map (algebraMap A₁ (A₁ ⊗[A] B)) ≤ RingHom.ker (tensorQuotientMap π hle)}
    (hJJ₁ : (RingHom.ker π.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A₁ ⊗[A] B).toRingHom ≤
        RingHom.ker (tensorQuotientMap π hle))
    (D : DividedPowerEnvelope A (algebraMap A B) (RingHom.ker π.toRingHom) hJ)
    (D₁ : DividedPowerEnvelope A₁ (algebraMap A₁ (A₁ ⊗[A] B))
      (RingHom.ker (tensorQuotientMap π hle)) hJ₁) :
    Function.Bijective (envelopeBaseChangeHom φ hφ hJJ₁ D D₁) :=
  bijective_envelopeBaseChangeHom_of_smooth π hπ hp hpA φ hφ (ker_tensorQuotientMap π hle hπ)
    hJJ₁ D D₁

end SmoothKernel

end Crystalline
