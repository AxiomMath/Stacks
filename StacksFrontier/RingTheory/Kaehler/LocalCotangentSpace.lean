module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.RingTheory.Smooth.Conormal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cotangent space of a local algebra with separable residue field extension

Let `R → A` be a local homomorphism of local rings whose extension of residue fields
`κ(R) → κ(A)` is separable.  The *relative cotangent space* of `R → A` is the `κ(A)`-vector
space `𝔪_A / (𝔪_R A + 𝔪_A²)`, and this file identifies it with the residue-field fibre
`κ(A) ⊗_A Ω[A⁄R]` of the module of relative Kähler differentials, by the map sending the class
of `a ∈ 𝔪_A` to `1 ⊗ da`.

## Main definitions

* `KaehlerDifferential.maximalIdealToTensorKaehler`: the map `𝔪_A → κ(A) ⊗_A Ω[A⁄R]`,
  `a ↦ 1 ⊗ da`.
* `KaehlerDifferential.relativeCotangentSpaceToTensorKaehler`: the map it induces on
  `𝔪_A / (𝔪_R A + 𝔪_A²)`.

## Main results

* `KaehlerDifferential.mem_map_maximalIdeal_add_sq_of_tmul_D_eq_zero`: an element of `𝔪_A` whose
  universal differential dies in the residue-field fibre already lies in `𝔪_R A + 𝔪_A²`.  This
  is the injectivity half.
* `KaehlerDifferential.bijective_relativeCotangentSpaceToTensorKaehler`: the map
  `𝔪_A / (𝔪_R A + 𝔪_A²) → κ(A) ⊗_A Ω[A⁄R]` is bijective.

## Implementation notes

The source of `KaehlerDifferential.relativeCotangentSpaceToTensorKaehler` is
`Deformation.relativeCotangentSpace (algebraMap R A)` of Tag 06GY, written out so that this file
stays inside commutative algebra.  The map itself is Mathlib's
`KaehlerDifferential.kerToTensor` restricted along `𝔪_A = ker (A → κ(A))`, so that its
`A`-linearity — which does use that the elements lie in that kernel — is not reproved.

Both halves of bijectivity reduce the base to a field.  For surjectivity this is only used
through `Ω[κ(A)⁄R] = 0`, which holds because `R → κ(R)` is surjective and `κ(R) → κ(A)` is
separable, so `κ(A)` is formally unramified over `R`; the surjection is then Mathlib's exact
sequence `𝔪_A/𝔪_A² → κ(A) ⊗_A Ω[A⁄R] → Ω[κ(A)⁄R]`.

Injectivity genuinely needs the base change: the map out of `𝔪_A/𝔪_A²` is *not* injective, its
kernel being the image of `𝔪_R A`, and the statement above is exactly that the kernel is no
larger.  Replacing `A` by `A' = A / 𝔪_R A`, an algebra over the field `κ(R)` with the same
residue field, the corresponding map `𝔪_{A'}/𝔪_{A'}² → κ(A) ⊗_{A'} Ω[A'⁄κ(R)]` *is* injective:
`κ(A)` is formally smooth over the field `κ(R)`, being separable, so Stacks 06A8
(`KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange`, which asks nothing of the
intermediate ring) applies.  The two maps are compared by the base change of
`KaehlerDifferential.map R κ(R) A A'`; that comparison is in fact an isomorphism, but only its
being defined is used.

The intermediate algebra structures on `A' = A / 𝔪_R A` are the ones of
`Ideal.Quotient.algebraQuotientOfLEComap`, whose structural maps are computed by the two `rfl`s
`hbase` and `hup` in the proof; the scalar towers are then checked on the image of `R`,
respectively of `A`.

## References

* [Stacks Project, Tag 0B2E](https://stacks.math.columbia.edu/tag/0B2E)
* [Stacks Project, Tag 06GY](https://stacks.math.columbia.edu/tag/06GY)
-/

@[expose] public section

open TensorProduct IsLocalRing KaehlerDifferential

namespace KaehlerDifferential

variable (R A : Type*) [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]

/-- **The canonical map `𝔪_A → κ(A) ⊗_A Ω[A⁄R]`** of Stacks Tag 0B2E, sending `a` to `1 ⊗ da`.
It is `KaehlerDifferential.kerToTensor` read through the identification of the maximal ideal of
a local ring with the kernel of its residue map. -/
@[sga "1 II 5.9" "partial"]
public noncomputable def maximalIdealToTensorKaehler :
    maximalIdeal A →ₗ[A] ResidueField A ⊗[A] Ω[A⁄R] :=
  (kerToTensor R A (ResidueField A)).comp
    (Submodule.inclusion IsLocalRing.ker_residue.ge)

omit [IsLocalRing R] [IsLocalHom (algebraMap R A)] in
/-- `KaehlerDifferential.maximalIdealToTensorKaehler` sends `a` to `1 ⊗ da`. -/
@[sga "1 II 5.9" "partial"]
public theorem maximalIdealToTensorKaehler_apply (a : maximalIdeal A) :
    maximalIdealToTensorKaehler R A a = 1 ⊗ₜ[A] D R A (a : A) :=
  rfl

/-- **`𝔪_R A + 𝔪_A²` is killed by `a ↦ 1 ⊗ da`.**  The differential of an element of `𝔪_R A` is
an `A`-linear combination of differentials of elements of `R`, hence zero, and the class of a
product of two elements of `𝔪_A` is zero in the conormal module. -/
@[sga "1 II 5.9" "partial"]
public theorem comap_le_ker_maximalIdealToTensorKaehler :
    (Submodule.comap (maximalIdeal A).subtype
        ((maximalIdeal R).map (algebraMap R A) + maximalIdeal A ^ 2) :
          Submodule A (maximalIdeal A)) ≤
      LinearMap.ker (maximalIdealToTensorKaehler R A) := by
  set J : Ideal A := RingHom.ker (algebraMap A (ResidueField A))
  have hJm : J = maximalIdeal A := IsLocalRing.ker_residue
  have hJsq : maximalIdeal A ^ 2 = J ^ 2 := by rw [hJm]
  set d : J →ₗ[A] ResidueField A ⊗[A] Ω[A⁄R] := kerToTensor R A (ResidueField A)
  have hd (a : J) : d a = 1 ⊗ₜ[A] D R A (a : A) := rfl
  have hIP : (maximalIdeal R).map (algebraMap R A) ≤ (LinearMap.ker d).map J.subtype := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    refine ⟨⟨algebraMap R A r, hJm.ge (IsLocalRing.map_maximalIdeal_le (algebraMap R A)
      (Ideal.mem_map_of_mem _ hr))⟩, ?_, rfl⟩
    show d _ = 0
    rw [hd]
    simp
  have hJP : maximalIdeal A ^ 2 ≤ (LinearMap.ker d).map J.subtype := by
    intro a ha
    have haj : a ∈ J := hJm.ge (Ideal.pow_le_self two_ne_zero ha)
    refine ⟨⟨a, haj⟩, ?_, rfl⟩
    show d ⟨a, haj⟩ = 0
    rw [show d ⟨a, haj⟩ =
      kerCotangentToTensor R A (ResidueField A) (J.toCotangent ⟨a, haj⟩) from rfl,
      (J.toCotangent_eq_zero _).2 (hJsq ▸ ha), map_zero]
  intro a ha
  obtain ⟨b, hb, hba⟩ :=
    (show (maximalIdeal R).map (algebraMap R A) + maximalIdeal A ^ 2 ≤
      (LinearMap.ker d).map J.subtype from sup_le hIP hJP) ha
  have hab : (⟨(b : A), hJm.le b.2⟩ : maximalIdeal A) = a := Subtype.ext hba
  show maximalIdealToTensorKaehler R A a = 0
  rw [← hab, maximalIdealToTensorKaehler_apply, ← hd b]
  exact hb

/-- **The canonical map `𝔪_A / (𝔪_R A + 𝔪_A²) → κ(A) ⊗_A Ω[A⁄R]`** of Stacks Tag 0B2E.  Its
source is the relative cotangent space `Deformation.relativeCotangentSpace (algebraMap R A)` of
Tag 06GY, and it sends the class of `a` to `1 ⊗ da`. -/
public noncomputable def relativeCotangentSpaceToTensorKaehler :
    ((maximalIdeal A) ⧸ (Submodule.comap (maximalIdeal A).subtype
        ((maximalIdeal R).map (algebraMap R A) + maximalIdeal A ^ 2) :
          Submodule A (maximalIdeal A))) →ₗ[A] ResidueField A ⊗[A] Ω[A⁄R] :=
  Submodule.liftQ _ (maximalIdealToTensorKaehler R A)
    (comap_le_ker_maximalIdealToTensorKaehler R A)

/-- `KaehlerDifferential.relativeCotangentSpaceToTensorKaehler` sends the class of `a ∈ 𝔪_A` to
`1 ⊗ da`. -/
public theorem relativeCotangentSpaceToTensorKaehler_mk (a : maximalIdeal A) :
    relativeCotangentSpaceToTensorKaehler R A (Submodule.Quotient.mk a) =
      1 ⊗ₜ[A] D R A (a : A) :=
  rfl

variable [Algebra.IsSeparable (ResidueField R) (ResidueField A)]

/-- **Injectivity half of Stacks Tag 0B2E.** If the universal relative differential of
`y ∈ 𝔪_A` becomes zero in the residue-field fibre `κ(A) ⊗_A Ω[A⁄R]`, then `y` already lies in
`𝔪_R A + 𝔪_A²`.  The hypothesis is that the residue field extension `κ(R) → κ(A)` is
separable. -/
@[ega "0 22.4.6" "special case", sga "1 II 5.9" "(i)"]
public theorem mem_map_maximalIdeal_add_sq_of_tmul_D_eq_zero
    {y : A} (hy : y ∈ maximalIdeal A)
    (h : (1 : ResidueField A) ⊗ₜ[A] D R A y = 0) :
    y ∈ (maximalIdeal R).map (algebraMap R A) + maximalIdeal A ^ 2 := by
  classical
  set Im : Ideal A := (maximalIdeal R).map (algebraMap R A)
  let : Algebra (ResidueField R) (A ⧸ Im) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : Algebra (A ⧸ Im) (ResidueField A) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (by simpa using IsLocalRing.map_maximalIdeal_le (algebraMap R A))
  have hbase (r : R) :
      algebraMap (ResidueField R) (A ⧸ Im) (residue R r) =
        Ideal.Quotient.mk Im (algebraMap R A r) := rfl
  have hup (z : A) :
      algebraMap (A ⧸ Im) (ResidueField A) (Ideal.Quotient.mk Im z) = residue A z := rfl
  have : IsScalarTower (ResidueField R) (A ⧸ Im) (ResidueField A) := by
    refine IsScalarTower.of_algebraMap_eq fun w => ?_
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective w
    rw [hbase, hup]
    exact (IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField A) r).symm
  have : SMulCommClass (ResidueField R) A (A ⧸ Im) :=
    ⟨fun c a w => by
      simp only [Algebra.smul_def]
      rw [mul_left_comm]⟩
  have : IsScalarTower R (ResidueField R) (A ⧸ Im) :=
    IsScalarTower.of_algebraMap_eq fun r => (hbase r).symm
  have : IsScalarTower A (A ⧸ Im) (ResidueField A) :=
    IsScalarTower.of_algebraMap_eq fun z => (hup z).symm
  -- the comparison of the two residue-field fibres, along `A → A / 𝔪_R A`
  let t : ResidueField A ⊗[A] Ω[A⁄R] →ₗ[ResidueField A]
      ResidueField A ⊗[A ⧸ Im] Ω[(A ⧸ Im)⁄(ResidueField R)] :=
    LinearMap.liftBaseChange (ResidueField A)
      ((TensorProduct.mk (A ⧸ Im) (ResidueField A)
        Ω[(A ⧸ Im)⁄(ResidueField R)] 1).restrictScalars A ∘ₗ
        KaehlerDifferential.map R (ResidueField R) A (A ⧸ Im))
  have ht (z : A) : t ((1 : ResidueField A) ⊗ₜ[A] D R A z) =
      (1 : ResidueField A) ⊗ₜ[A ⧸ Im]
        D (ResidueField R) (A ⧸ Im) (Ideal.Quotient.mk Im z) := by
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    exact congrArg (fun w => (1 : ResidueField A) ⊗ₜ[A ⧸ Im] w)
      (KaehlerDifferential.map_D R (ResidueField R) A (A ⧸ Im) z)
  -- the kernel of `A / 𝔪_R A → κ(A)` is the image of `𝔪_A`
  have hsurj : Function.Surjective (algebraMap (A ⧸ Im) (ResidueField A)) := fun w => by
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective w
    exact ⟨Ideal.Quotient.mk Im z, hup z⟩
  have hmem (z : A) : Ideal.Quotient.mk Im z ∈ RingHom.ker (algebraMap (A ⧸ Im) (ResidueField A)) ↔
      z ∈ maximalIdeal A := by
    rw [RingHom.mem_ker, hup, residue_eq_zero_iff]
  have hker : RingHom.ker (algebraMap (A ⧸ Im) (ResidueField A)) =
      (maximalIdeal A).map (Ideal.Quotient.mk Im) := by
    refine le_antisymm (fun w hw => ?_) (Ideal.map_le_iff_le_comap.2 fun z hz => (hmem z).2 hz)
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    exact Ideal.mem_map_of_mem _ ((hmem z).1 hw)
  have : Algebra.FormallySmooth (ResidueField R) (ResidueField A) := by
    have := Algebra.FormallyEtale.of_isSeparable (ResidueField R) (ResidueField A)
    infer_instance
  have hyJ := (hmem y).2 hy
  have hzero : (RingHom.ker (algebraMap (A ⧸ Im) (ResidueField A))).toCotangent
      ⟨Ideal.Quotient.mk Im y, hyJ⟩ = 0 := by
    refine (KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange
      (ResidueField R) (A ⧸ Im) (ResidueField A) hsurj).1 ?_
    rw [kerCotangentToTensor_toCotangent, map_zero, ← ht y, h, map_zero]
  rw [Ideal.toCotangent_eq_zero] at hzero
  have hsq : Ideal.Quotient.mk Im y ∈
      ((maximalIdeal A).map (Ideal.Quotient.mk Im)) ^ 2 := by
    rw [← hker]
    exact hzero
  rw [← Ideal.map_pow, Ideal.mem_quotient_iff_mem_sup] at hsq
  rwa [Ideal.add_eq_sup, sup_comm]

/-- **Stacks Project, Tag 0B2E.**  For a local homomorphism `R → A` of local rings with
separable residue field extension, the canonical map
`𝔪_A / (𝔪_R A + 𝔪_A²) → κ(A) ⊗_A Ω[A⁄R]`, `a ↦ 1 ⊗ da`, is bijective: the relative cotangent
space of `R → A` is the residue-field fibre of the module of relative differentials. -/
@[ega "0 22.4.6" "special case"]
public theorem bijective_relativeCotangentSpaceToTensorKaehler :
    Function.Bijective (relativeCotangentSpaceToTensorKaehler R A) := by
  set P : Submodule A (maximalIdeal A) := Submodule.comap (maximalIdeal A).subtype
    ((maximalIdeal R).map (algebraMap R A) + maximalIdeal A ^ 2)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := P.mkQ_surjective z
    refine (Submodule.Quotient.mk_eq_zero P).2 ?_
    show (a : A) ∈ (maximalIdeal R).map (algebraMap R A) + maximalIdeal A ^ 2
    exact mem_map_maximalIdeal_add_sq_of_tmul_D_eq_zero R A a.2
      (relativeCotangentSpaceToTensorKaehler_mk R A a ▸ hz)
  · have : Algebra.FormallyUnramified R (ResidueField R) :=
      Algebra.FormallyUnramified.of_surjective (Algebra.ofId R (ResidueField R))
        IsLocalRing.residue_surjective
    have : Algebra.FormallyUnramified (ResidueField R) (ResidueField A) :=
      Algebra.FormallyUnramified.of_isSeparable _ _
    have : Algebra.FormallyUnramified R (ResidueField A) :=
      Algebra.FormallyUnramified.comp R (ResidueField R) (ResidueField A)
    have : Subsingleton Ω[(ResidueField A)⁄R] :=
      Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
    intro z
    obtain ⟨w, hw⟩ := (exact_kerCotangentToTensor_mapBaseChange R A (ResidueField A)
      IsLocalRing.residue_surjective z).mp (Subsingleton.elim _ _)
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ w
    exact ⟨Submodule.Quotient.mk ⟨(a : A), IsLocalRing.ker_residue.le a.2⟩, hw⟩

end KaehlerDifferential

end
