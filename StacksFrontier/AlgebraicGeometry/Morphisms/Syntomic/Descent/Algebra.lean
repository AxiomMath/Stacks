module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatDescent
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt

/-!
# Complete-intersection closed fibres in a tower of local rings

Let `R → A → B` be local homomorphisms of local rings, with `A → B` flat and with both maps
essentially of finite type. Write `κ(R)` for the residue field of `R`. If the closed fibre
`κ(R) ⊗_R B` of `R → B` is a complete intersection over `κ(R)`, then so is the closed fibre
`κ(R) ⊗_R A` of `R → A`, and the closed fibre `κ(A) ⊗_A B` of `A → B` is a complete
intersection over `κ(A)`.

This is Avramov's theorem, `LocalCompleteIntersection.isCompleteIntersectionRing_iff_of_flat`,
read on the closed fibres over `R`: the induced map `κ(R) ⊗_R A → κ(R) ⊗_R B` is again a flat
local homomorphism of Noetherian local rings, its source and target are the two closed fibres
over `R`, and its own closed fibre is `κ(A) ⊗_A B`.

## Main results

* `LocalCompleteIntersection.isCompleteIntersection_iff_isCompleteIntersectionRing`: for a
  Noetherian local algebra essentially of finite type over a field, being a complete
  intersection over that field is the intrinsic complete-intersection condition on the ring.
* `LocalCompleteIntersection.isCompleteIntersection_closedFibre_base_of_flat`: the closed fibre
  of `R → A` is a complete intersection over `κ(R)`.
* `LocalCompleteIntersection.isCompleteIntersection_closedFibre_of_flat`: the closed fibre of
  `A → B` is a complete intersection over `κ(A)`.

## Implementation notes

The closed fibre of a local homomorphism `R → S` is `κ(R) ⊗_R S`, which Mathlib already knows
to be a local ring and which is the quotient `S / 𝔪_R S`: the canonical surjection
`S → κ(R) ⊗_R S` is `Algebra.TensorProduct.includeRight`, and `ker_includeRight_residueField`
computes its kernel as `𝔪_R S`. The identification of the closed fibre of
`κ(R) ⊗_R A → κ(R) ⊗_R B` with `κ(A) ⊗_A B` is obtained from these two surjections: both rings
are the quotient of `B` by the same ideal `𝔪_A B`.

Essential finite type over the residue field enters only through Noetherianity of the fibres
and through the comparison of the two complete-intersection conditions. No Noetherian
hypothesis is placed on `R`, `A` or `B` themselves, and `R → A` is not assumed flat.

## References

* [Stacks Project, Tag 09Q7](https://stacks.math.columbia.edu/tag/09Q7)
* [Stacks Project, Tag 09Q6](https://stacks.math.columbia.edu/tag/09Q6)
* [Stacks Project, Tag 00SD](https://stacks.math.columbia.edu/tag/00SD)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u

namespace LocalCompleteIntersection

/-! ### The two complete-intersection conditions on a local algebra over a field -/

/-- For a Noetherian local algebra `A` essentially of finite type over a field `k`, being a
complete intersection over `k` in the sense of Definition 00SD is the same as being a complete
intersection ring in the intrinsic sense of 09Q3.

Both conditions only depend on the isomorphism class of `A`, and
`CompleteIntersection.exists_finiteType_isLocalization_atPrime` presents `A` as the localization
at a prime of a finite type `k`-algebra, where the two conditions agree by Lemma 09Q6. -/
theorem isCompleteIntersection_iff_isCompleteIntersectionRing
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [IsLocalRing A] [Algebra.EssFiniteType k A] :
    IsCompleteIntersection k A ↔ IsCompleteIntersectionRing A := by
  obtain ⟨n, J, _, _, q, _, _⟩ :=
    CompleteIntersection.exists_finiteType_isLocalization_atPrime k A
  let T := MvPolynomial (Fin n) k ⧸ J
  let eA : Localization.AtPrime q ≃ₐ[T] A :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) A
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ (Algebra.FiniteType.isNoetherianRing k T)
  have : IsLocalRing (Localization.AtPrime q) := IsLocalization.AtPrime.isLocalRing _ q
  have key := isCompleteIntersection_atPrime_iff_isCompleteIntersectionRing k T q
  exact ⟨fun h => isCompleteIntersectionRing_of_ringEquiv eA.toRingEquiv
      (key.mp (h.of_algEquiv (eA.symm.restrictScalars k))),
    fun h => (key.mpr (isCompleteIntersectionRing_of_ringEquiv eA.symm.toRingEquiv h)).of_algEquiv
      (eA.restrictScalars k)⟩

/-! ### The closed fibre of a local homomorphism -/

/-- The canonical map `S → κ(R) ⊗_R S` onto the closed fibre of a ring map `R → S` out of a
local ring is surjective, the residue map of `R` being surjective. -/
theorem surjective_includeRight_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    Function.Surjective (Algebra.TensorProduct.includeRight :
      S →ₐ[R] ResidueField R ⊗[R] S).toRingHom :=
  TensorProduct.mk_surjective R S (ResidueField R) residue_surjective

/-- The kernel of the canonical surjection `S → κ(R) ⊗_R S` onto the closed fibre of a ring map
`R → S` out of a local ring is the ideal `𝔪_R S` generated by the maximal ideal of `R`. -/
theorem ker_includeRight_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    RingHom.ker (Algebra.TensorProduct.includeRight :
        S →ₐ[R] ResidueField R ⊗[R] S).toRingHom =
      (maximalIdeal R).map (algebraMap R S) := by
  ext s
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  exact map_eq_zero_iff
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R))
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R)).injective
    (x := Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) s)

/-- The closed fibre `κ(R) ⊗_R S` of a ring map `R → S` essentially of finite type is
essentially of finite type over `κ(R)`. -/
private theorem essFiniteType_residueField_tensorProduct (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] :
    Algebra.EssFiniteType (ResidueField R) (ResidueField R ⊗[R] S) :=
  RingHom.essFiniteType_algebraMap.mp
    (RingHom.EssFiniteType.isStableUnderBaseChange.tensorProduct (ResidueField R)
      (RingHom.essFiniteType_algebraMap.mpr inferInstance))

/-! ### The closed fibres of a tower of local homomorphisms -/

/-- A composite of local homomorphisms `R → A → B` is a local homomorphism `R → B`. -/
private theorem isLocalHom_algebraMap_of_tower (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)] :
    IsLocalHom (algebraMap R B) := by
  rw [IsScalarTower.algebraMap_eq R A B]
  infer_instance

section Tower

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [IsLocalRing R] [IsLocalRing A] [IsLocalRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)]

/-- The map `κ(R) ⊗_R A → κ(R) ⊗_R B` of closed fibres over `R` induced by `A → B`. -/
noncomputable def closedFibreMap :
    (ResidueField R ⊗[R] A) →ₐ[ResidueField R] (ResidueField R ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R))
    (IsScalarTower.toAlgHom R A B)

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)] in
/-- The map of closed fibres over `R` is compatible with the canonical surjections from `A` and
from `B`. -/
@[simp]
theorem closedFibreMap_includeRight (a : A) :
    closedFibreMap R A B (Algebra.TensorProduct.includeRight a) =
      Algebra.TensorProduct.includeRight (algebraMap A B a) := by
  simp [closedFibreMap]

omit [IsLocalRing A] in
/-- The map of closed fibres over `R` is a local homomorphism: the canonical surjections onto
the two fibres are local homomorphisms, as is `A → B`, and the resulting square commutes. -/
theorem isLocalHom_closedFibreMap : IsLocalHom (closedFibreMap R A B).toRingHom := by
  have hRB := isLocalHom_algebraMap_of_tower R A B
  refine ⟨fun z hz => ?_⟩
  obtain ⟨a, rfl⟩ := surjective_includeRight_residueField R A z
  have hz' : IsUnit ((Algebra.TensorProduct.includeRight :
      B →ₐ[R] ResidueField R ⊗[R] B) (algebraMap A B a)) := by
    rw [← closedFibreMap_includeRight R A B a]
    exact hz
  have hB : IsLocalHom (Algebra.TensorProduct.includeRight :
      B →ₐ[R] ResidueField R ⊗[R] B).toRingHom :=
    IsLocalHom.of_surjective _ (surjective_includeRight_residueField R B)
  exact ((isUnit_map_iff (algebraMap A B) a).mp
    ((isUnit_map_iff (Algebra.TensorProduct.includeRight :
      B →ₐ[R] ResidueField R ⊗[R] B).toRingHom _).mp hz')).map
    (Algebra.TensorProduct.includeRight : A →ₐ[R] ResidueField R ⊗[R] A).toRingHom

/-- The closed fibre of the map of closed fibres over `R` is the closed fibre of `A → B`: both
are the quotient of `B` by the ideal `𝔪_A B`. -/
noncomputable def closedFibreQuotientEquiv :
    ((ResidueField R ⊗[R] B) ⧸
        Ideal.map (closedFibreMap R A B).toRingHom
          (maximalIdeal (ResidueField R ⊗[R] A))) ≃+* (ResidueField A ⊗[A] B) := by
  have hsurjB := surjective_includeRight_residueField R B
  have hmaxA : Ideal.map (Algebra.TensorProduct.includeRight :
        A →ₐ[R] ResidueField R ⊗[R] A).toRingHom (maximalIdeal A) =
      maximalIdeal (ResidueField R ⊗[R] A) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ (surjective_includeRight_residueField R A)
  have hsq : (closedFibreMap R A B).toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] ResidueField R ⊗[R] A).toRingHom =
      (Algebra.TensorProduct.includeRight :
        B →ₐ[R] ResidueField R ⊗[R] B).toRingHom.comp (algebraMap A B) :=
    RingHom.ext fun a => closedFibreMap_includeRight R A B a
  set J := Ideal.map (closedFibreMap R A B).toRingHom
    (maximalIdeal (ResidueField R ⊗[R] A)) with hJdef
  have hJ : J = Ideal.map (Algebra.TensorProduct.includeRight :
      B →ₐ[R] ResidueField R ⊗[R] B).toRingHom
      ((maximalIdeal A).map (algebraMap A B)) := by
    rw [hJdef, ← hmaxA, Ideal.map_map, Ideal.map_map, hsq]
  set ρ : B →+* ((ResidueField R ⊗[R] B) ⧸ J) :=
    (Ideal.Quotient.mk J).comp (Algebra.TensorProduct.includeRight :
      B →ₐ[R] ResidueField R ⊗[R] B).toRingHom with hρdef
  have hle : (maximalIdeal R).map (algebraMap R B) ≤
      (maximalIdeal A).map (algebraMap A B) := by
    calc (maximalIdeal R).map (algebraMap R B)
        = ((maximalIdeal R).map (algebraMap R A)).map (algebraMap A B) := by
          rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      _ ≤ (maximalIdeal A).map (algebraMap A B) :=
          Ideal.map_mono (IsLocalRing.map_maximalIdeal_le (algebraMap R A))
  have hker : RingHom.ker ρ = (maximalIdeal A).map (algebraMap A B) := by
    rw [hρdef, ← RingHom.comap_ker, Ideal.mk_ker, hJ,
      Ideal.comap_map_of_surjective _ hsurjB, ← RingHom.ker_eq_comap_bot,
      ker_includeRight_residueField R B, sup_eq_left.mpr hle]
  exact ((Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hsurjB))).symm.trans
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)).toRingEquiv

variable [Module.Flat A B] [Algebra.EssFiniteType R A] [Algebra.EssFiniteType A B]

/-- **Avramov's theorem on the closed fibres of a tower.** If the closed fibre of `R → B` is a
complete intersection over `κ(R)`, then the closed fibre of `R → A` is a complete intersection
over `κ(R)` and the closed fibre of `A → B` is a complete intersection over `κ(A)`. -/
private theorem isCompleteIntersection_closedFibre_pair_of_flat
    (h : IsCompleteIntersection (ResidueField R) (ResidueField R ⊗[R] B)) :
    IsCompleteIntersection (ResidueField R) (ResidueField R ⊗[R] A) ∧
      IsCompleteIntersection (ResidueField A) (ResidueField A ⊗[A] B) := by
  have hRB := isLocalHom_algebraMap_of_tower R A B
  have hessRB : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R A B
  have := essFiniteType_residueField_tensorProduct R A
  have := essFiniteType_residueField_tensorProduct R B
  have := essFiniteType_residueField_tensorProduct A B
  have hnA : IsNoetherianRing (ResidueField R ⊗[R] A) :=
    Algebra.EssFiniteType.isNoetherianRing (ResidueField R) _
  have hnB : IsNoetherianRing (ResidueField R ⊗[R] B) :=
    Algebra.EssFiniteType.isNoetherianRing (ResidueField R) _
  have hnF : IsNoetherianRing (ResidueField A ⊗[A] B) :=
    Algebra.EssFiniteType.isNoetherianRing (ResidueField A) _
  let _ : Algebra (ResidueField R ⊗[R] A) (ResidueField R ⊗[R] B) :=
    (closedFibreMap R A B).toRingHom.toAlgebra
  have hlocmap :
      IsLocalHom (algebraMap (ResidueField R ⊗[R] A) (ResidueField R ⊗[R] B)) :=
    isLocalHom_closedFibreMap R A B
  have hflatmap : Module.Flat (ResidueField R ⊗[R] A) (ResidueField R ⊗[R] B) :=
    RingHom.flat_algebraMap_iff.mp
      (RingHom.Flat.tensorProductMap (RingHom.Flat.id (ResidueField R))
        (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A B›))
  have hBring : IsCompleteIntersectionRing (ResidueField R ⊗[R] B) :=
    (isCompleteIntersection_iff_isCompleteIntersectionRing _ _).mp h
  refine ⟨(isCompleteIntersection_iff_isCompleteIntersectionRing _ _).mpr
    (isCompleteIntersectionRing_of_flat _ _ hBring), ?_⟩
  set J := Ideal.map (closedFibreMap R A B).toRingHom (maximalIdeal (ResidueField R ⊗[R] A))
  have _ : Nontrivial ((ResidueField R ⊗[R] B) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (IsLocalRing.map_maximalIdeal_lt_top
      (algebraMap (ResidueField R ⊗[R] A) (ResidueField R ⊗[R] B))).ne
  have _ : IsLocalRing ((ResidueField R ⊗[R] B) ⧸ J) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have _ : IsNoetherianRing ((ResidueField R ⊗[R] B) ⧸ J) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  exact (isCompleteIntersection_iff_isCompleteIntersectionRing _ _).mpr
    (isCompleteIntersectionRing_of_ringEquiv (closedFibreQuotientEquiv R A B)
      (isCompleteIntersectionRing_quotient_of_flat
        (ResidueField R ⊗[R] A) (ResidueField R ⊗[R] B) hBring))

/-- If the closed fibre of `R → B` is a complete intersection over `κ(R)`, then so is the closed
fibre of `R → A`: the induced map of closed fibres over `R` is a flat local homomorphism of
Noetherian local rings, and a complete intersection descends along such a map. -/
theorem isCompleteIntersection_closedFibre_base_of_flat
    (h : IsCompleteIntersection (ResidueField R) (ResidueField R ⊗[R] B)) :
    IsCompleteIntersection (ResidueField R) (ResidueField R ⊗[R] A) :=
  (isCompleteIntersection_closedFibre_pair_of_flat R A B h).1

/-- If the closed fibre of `R → B` is a complete intersection over `κ(R)`, then the closed fibre
of `A → B` is a complete intersection over `κ(A)`: it is the closed fibre of the induced flat
local homomorphism of the closed fibres over `R`. -/
theorem isCompleteIntersection_closedFibre_of_flat
    (h : IsCompleteIntersection (ResidueField R) (ResidueField R ⊗[R] B)) :
    IsCompleteIntersection (ResidueField A) (ResidueField A ⊗[A] B) :=
  (isCompleteIntersection_closedFibre_pair_of_flat R A B h).2

end Tower

end LocalCompleteIntersection
