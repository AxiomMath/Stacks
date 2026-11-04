module

public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Lengths along regular ring maps

Let `R → R'` be a local homomorphism of local rings which is regular (**Stacks 07BZ**) and whose
target is Artinian. The closed fibre `R' / 𝔪_R R'` is then a regular ring which is local and
Artinian, hence a field, so `𝔪_R R' = 𝔪_{R'}`, and the length identity of **Stacks 02M1** gives
`length_R R = length_{R'} R'`.

Localizing a regular map `C → A` with Noetherian target at a minimal prime `𝔭` of `A` yields such a
homomorphism `C_𝔮 → A_𝔭` with `𝔮 = 𝔭 ∩ C` (**Stacks 07C0**), so the two local rings have the same
length. For a Noetherian local G-ring `C` the completion map `C → C^∧` is regular, and the
multiplicity of an irreducible component of `Spec C` therefore agrees with the multiplicity of
every irreducible component of `Spec C^∧` lying over it. This is the commutative-algebra core of
**Stacks 0DRD**.

## Main results

* `extendedMaximalIdeal_eq_maximalIdeal_of_isRegularRingHom`: for a regular local homomorphism
  `R → R'` with `R'` Artinian, `𝔪_R R' = 𝔪_{R'}`.
* `length_eq_length_of_isRegularRingHom`: under the same hypotheses
  `length_R R = length_{R'} R'`.
* `length_localization_comap_eq_of_isRegularRingHom`: for a regular map `f : C → A` with `A`
  Noetherian and a minimal prime `𝔭` of `A`, the localizations `C_{f⁻¹ 𝔭}` and `A_𝔭` have the
  same length.
* `length_localization_comap_eq_of_isGRing`: the case of the completion of a Noetherian local
  G-ring.

## References

* [Stacks Project, Tag 0DRD](https://stacks.math.columbia.edu/tag/0DRD)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 07C0](https://stacks.math.columbia.edu/tag/07C0)
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v

/-- The quotient of an `R`-algebra `R'` by the extension of a maximal ideal `𝔪` of `R` is the
fibre `κ(𝔪) ⊗[R] R'` of `R'` over `𝔪`. -/
def Ideal.quotientMapRingEquivFiber {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    [Algebra R R'] (m : Ideal R) [m.IsMaximal] :
    R' ⧸ m.map (algebraMap R R') ≃+* m.Fiber R' :=
  let e : (R ⧸ m) ≃ₐ[R] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R' m).toRingEquiv.trans
    (Algebra.TensorProduct.comm R R' (R ⧸ m)).toRingEquiv).trans
    (Algebra.TensorProduct.congr e AlgEquiv.refl).toRingEquiv

/-- **The closed fibre of a regular local homomorphism with Artinian target is a field.** For a
local homomorphism `R → R'` of local rings which is regular, with `R'` Artinian, the extension of
the maximal ideal of `R` is the maximal ideal of `R'`. -/
theorem extendedMaximalIdeal_eq_maximalIdeal_of_isRegularRingHom
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [Algebra R R'] [IsLocalRing R]
    [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsArtinianRing R']
    (h : IsRegularRingHom (algebraMap R R')) :
    extendedMaximalIdeal R R' = maximalIdeal R' := by
  have hfib := (isRegularRingHom_algebraMap_iff.mp h).2 (maximalIdeal R)
  have : IsRegularRing ((maximalIdeal R).Fiber R') :=
    isRegularRing_of_isGeometricallyRegular hfib.2
  have : IsRegularRing (R' ⧸ extendedMaximalIdeal R R') :=
    IsRegularRing.of_ringEquiv ((maximalIdeal R).quotientMapRingEquivFiber (R' := R')).symm
  have : Nontrivial (R' ⧸ extendedMaximalIdeal R R') :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top _).ne
  have : IsLocalRing (R' ⧸ extendedMaximalIdeal R R') :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsRegularLocalRing (R' ⧸ extendedMaximalIdeal R R') :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  have : IsDomain (R' ⧸ extendedMaximalIdeal R R') := IsRegularLocalRing.isDomain _
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isReduced_of_isLocalRing _))

/-- **Length is preserved along a regular local homomorphism with Artinian target.** For a local
homomorphism `R → R'` of local rings which is regular, with `R'` Artinian,
`length_R R = length_{R'} R'`. -/
theorem length_eq_length_of_isRegularRingHom
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [Algebra R R'] [IsLocalRing R]
    [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsArtinianRing R']
    (h : IsRegularRingHom (algebraMap R R')) :
    Module.length R R = Module.length R' R' := by
  have : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp
    (isRegularRingHom_algebraMap_iff.mp h).1
  have hfactor : Module.length R' (R' ⧸ extendedMaximalIdeal R R') = 1 := by
    rw [extendedMaximalIdeal_eq_maximalIdeal_of_isRegularRingHom R R' h]
    have hsurj : Function.Surjective (algebraMap R' (R' ⧸ maximalIdeal R')) := by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective
    let := Ideal.Quotient.field (maximalIdeal R')
    have : IsSimpleModule R' (R' ⧸ maximalIdeal R') :=
      (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hsurj).2 inferInstance
    exact Module.length_eq_one R' _
  have key := length_baseChange_eq_length_mul_length_quotient R R' R
  rwa [(TensorProduct.AlgebraTensorModule.rid R R' R').length_eq, hfactor, mul_one] at key

/-- **Length of localizations at minimal primes along a regular map.** Let `f : C → A` be a
regular ring map with `A` Noetherian and let `𝔭` be a minimal prime of `A`, lying over
`𝔮 = f⁻¹ 𝔭`. Then `length_{C_𝔮} C_𝔮 = length_{A_𝔭} A_𝔭`. -/
theorem length_localization_comap_eq_of_isRegularRingHom
    {C : Type u} {A : Type v} [CommRing C] [CommRing A] [IsNoetherianRing A]
    (f : C →+* A) (hf : IsRegularRingHom f) (P : Ideal A) (hP : P ∈ minimalPrimes A) :
    letI : P.IsPrime := hP.1.1
    Module.length (Localization.AtPrime (P.comap f)) (Localization.AtPrime (P.comap f)) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) := by
  have : P.IsPrime := hP.1.1
  let g := Localization.localRingHom (P.comap f) P f rfl
  have hg : IsRegularRingHom g := by
    have h12 := (isRegularRingHom_tfae_localizations f).out 1 2
    exact h12.mp hf (P.comap f) P rfl
  let : Algebra (Localization.AtPrime (P.comap f)) (Localization.AtPrime P) := g.toAlgebra
  have : IsLocalHom (algebraMap (Localization.AtPrime (P.comap f)) (Localization.AtPrime P)) :=
    (inferInstance : IsLocalHom g)
  have : Ring.KrullDimLE 0 (Localization.AtPrime P) :=
    Ring.KrullDimLE.of_isLocalization P hP _
  have : IsNoetherianRing (Localization.AtPrime P) := by
    unfold Localization.AtPrime; infer_instance
  have : IsArtinianRing (Localization.AtPrime P) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact length_eq_length_of_isRegularRingHom _ _ hg

/-- **Multiplicities of components along the completion of a local G-ring** (the
commutative-algebra core of **Stacks 0DRD**). Let `C` be a Noetherian local ring which is a G-ring
and let `𝔭` be a minimal prime of its completion `C^∧`, lying over `𝔮 = 𝔭 ∩ C`. Then the local
rings `C_𝔮` and `(C^∧)_𝔭` have the same length: the irreducible component of `Spec C^∧` cut out by
`𝔭` has the same multiplicity as the irreducible component of `Spec C` cut out by `𝔮`. -/
theorem length_localization_comap_eq_of_isGRing
    (C : Type u) [CommRing C] [IsLocalRing C] (hC : IsGRing C)
    (P : Ideal (AdicCompletion (maximalIdeal C) C))
    (hP : P ∈ minimalPrimes (AdicCompletion (maximalIdeal C) C)) :
    letI : P.IsPrime := hP.1.1
    Module.length (Localization.AtPrime (P.comap (algebraMap C _)))
        (Localization.AtPrime (P.comap (algebraMap C _))) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) := by
  have : IsNoetherianRing C := hC.1
  exact length_localization_comap_eq_of_isRegularRingHom _
    ((isGRing_iff_isRegularRingHom_completion C).mp hC) P hP

end
