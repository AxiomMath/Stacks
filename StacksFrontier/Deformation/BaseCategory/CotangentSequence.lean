module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.CotangentHomology

/-!
# The four-term exact sequence of a residue surjection

Let `Λ` be a ring, let `k` be a field and let `A` be a `Λ`-algebra equipped with a `Λ`-algebra
surjection `A → k` — for instance an object of the base category `𝒞_Λ`, whose residue map is
such a surjection. Write `𝔪_A` for the kernel of `A → k`. There is a canonical exact sequence

    H₁(L_{k/Λ}) ⟶ 𝔪_A/𝔪_A² ⟶ Ω_{A/Λ} ⊗_A k ⟶ Ω_{k/Λ} ⟶ 0,

the Jacobi–Zariski sequence of `Λ → A → k` with the term `H₁(L_{k/A})` rewritten as `𝔪_A/𝔪_A²`
and the term `Ω_{k/A}`, which vanishes because `A → k` is surjective, dropped. The middle map
is the differential `d_A`, sending the class of `f ∈ 𝔪_A` to `1 ⊗ d f`.

## Main definitions

* `Deformation.cotangentEquivH1Cotangent`: the identification `𝔪_A/𝔪_A² = H₁(L_{k/A})`.
* `Deformation.h1CotangentToCotangent`: the leftmost map `H₁(L_{k/Λ}) → 𝔪_A/𝔪_A²`, the
  functoriality map of the naive cotangent complex read through that identification.

## Main results

* `Deformation.δ_comp_cotangentEquivH1Cotangent`: the Jacobi–Zariski connecting map, read on
  `𝔪_A/𝔪_A²` through the identification, is the differential `d_A`.
* `Deformation.exact_h1CotangentToCotangent`: exactness at `𝔪_A/𝔪_A²`.
* `Deformation.exact_cotangentSequence`: **Stacks 06S7**, the whole four-term sequence.

## Implementation notes

The tensor factors are ordered as in Mathlib, so the third term is `k ⊗_A Ω_{A/Λ}` and the
differential `d_A` is `KaehlerDifferential.kerCotangentToTensor Λ A k`, while the map to
`Ω_{k/Λ}` is `KaehlerDifferential.mapBaseChange Λ A k`. Exactness at `k ⊗_A Ω_{A/Λ}` and
surjectivity onto `Ω_{k/Λ}` are then Mathlib's three-term sequence of a surjection; the content
here is the leftmost spot, which needs the identification `𝔪_A/𝔪_A² = H₁(L_{k/A})` of
Stacks 06S9 together with the fact that it carries the connecting map to `d_A`.

Since `𝔪_A/𝔪_A²` carries no `k`-action on the nose, the maps out of and into it are recorded as
`A`-linear; the sequence is one of `k`-modules after transport along `A → k`.

## References

* [Stacks Project, Tag 06S7](https://stacks.math.columbia.edu/tag/06S7)
-/

@[expose] public section

open Algebra KaehlerDifferential MvPolynomial
open scoped TensorProduct

namespace Deformation

universe u v w

variable {Λ : Type u} {A : Type v} {k : Type w}
  [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra Λ k] [Algebra A k]
  [IsScalarTower Λ A k]

/-- For a surjection `A → k` with kernel `𝔪_A`, the class of `C a` in the conormal module of
the polynomial presentation of `k` over `A` lies in the kernel of its structure map. -/
private theorem C_mem_ker_self (x : RingHom.ker (algebraMap A k)) :
    C x.1 ∈ (Algebra.Generators.self A k).ker := by
  simpa [Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
    using RingHom.mem_ker.mp x.2

/-- For a `Λ`-algebra surjection `A → k` with kernel `𝔪_A`, the conormal module `𝔪_A/𝔪_A²` is
the first homology of the naive cotangent complex of `k` over `A`. -/
public noncomputable def cotangentEquivH1Cotangent
    (h : Function.Surjective (algebraMap A k)) :
    (RingHom.ker (algebraMap A k)).Cotangent ≃ₗ[A] Algebra.H1Cotangent A k :=
  LinearEquiv.ofBijective _ (conormalToH1Cotangent_bijective_of_surjective (Λ := A) (k := k) h)

/-- The Jacobi–Zariski connecting map of `Λ → A → k` sends the class of `f ∈ 𝔪_A`, viewed in
`H₁(L_{k/A})`, to the pure tensor `1 ⊗ d f` of `k ⊗_A Ω_{A/Λ}`. -/
public theorem δ_cotangentEquivH1Cotangent_toCotangent
    (h : Function.Surjective (algebraMap A k)) (x : RingHom.ker (algebraMap A k)) :
    Algebra.H1Cotangent.δ Λ A k
        (cotangentEquivH1Cotangent h ((RingHom.ker (algebraMap A k)).toCotangent x)) =
      1 ⊗ₜ[A] D Λ A x.1 := by
  have hid : Algebra.H1Cotangent.map A A k k = LinearMap.id :=
    (Algebra.Extension.H1Cotangent.map_eq _ (.id _)).trans
      Algebra.Extension.H1Cotangent.map_id
  have h1 : cotangentEquivH1Cotangent h ((RingHom.ker (algebraMap A k)).toCotangent x) =
      ⟨Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self A k).toExtension)
        ⟨C x.1, C_mem_ker_self x⟩,
       Algebra.Extension.Cotangent.mk_C_mem_ker_cotangentComplex _ (C_mem_ker_self x)⟩ := by
    apply Algebra.Extension.h1Cotangentι_ext
    change _ = Algebra.Extension.Cotangent.mk _
    rw [cotangentEquivH1Cotangent, LinearEquiv.ofBijective_apply, conormalToH1Cotangent]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, hid,
      LinearMap.id_coe, id_eq]
    rfl
  rw [h1]
  exact Algebra.Generators.H1Cotangent.δ_C _ _ (C_mem_ker_self x)

/-- Read on `𝔪_A/𝔪_A²` through the identification with `H₁(L_{k/A})`, the Jacobi–Zariski
connecting map of `Λ → A → k` is the differential `d_A : 𝔪_A/𝔪_A² → Ω_{A/Λ} ⊗_A k`. -/
public theorem δ_comp_cotangentEquivH1Cotangent
    (h : Function.Surjective (algebraMap A k)) :
    (Algebra.H1Cotangent.δ Λ A k).restrictScalars A ∘ₗ
        (cotangentEquivH1Cotangent h).toLinearMap =
      KaehlerDifferential.kerCotangentToTensor Λ A k := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, kerCotangentToTensor_toCotangent]
    using δ_cotangentEquivH1Cotangent_toCotangent (Λ := Λ) h x

/-- The leftmost map `H₁(L_{k/Λ}) → 𝔪_A/𝔪_A²` of the four-term sequence of `Λ → A → k`: the
functoriality map `H₁(L_{k/Λ}) → H₁(L_{k/A})` of the naive cotangent complex, read through the
identification of `H₁(L_{k/A})` with the conormal module of `A → k`. -/
public noncomputable def h1CotangentToCotangent (Λ : Type u) [CommRing Λ] [Algebra Λ A]
    [Algebra Λ k] [IsScalarTower Λ A k] (h : Function.Surjective (algebraMap A k)) :
    Algebra.H1Cotangent Λ k →ₗ[A] (RingHom.ker (algebraMap A k)).Cotangent :=
  (cotangentEquivH1Cotangent h).symm.toLinearMap ∘ₗ
    (Algebra.H1Cotangent.map Λ A k k).restrictScalars A

/-- The sequence `H₁(L_{k/Λ}) → 𝔪_A/𝔪_A² → Ω_{A/Λ} ⊗_A k` is exact: this is the exactness of
the Jacobi–Zariski sequence of `Λ → A → k` at `H₁(L_{k/A})`, transported along the
identification of `H₁(L_{k/A})` with `𝔪_A/𝔪_A²`. -/
public theorem exact_h1CotangentToCotangent (h : Function.Surjective (algebraMap A k)) :
    Function.Exact (h1CotangentToCotangent Λ h)
      (KaehlerDifferential.kerCotangentToTensor Λ A k) := by
  have hex : Function.Exact ((Algebra.H1Cotangent.map Λ A k k).restrictScalars A)
      ((Algebra.H1Cotangent.δ Λ A k).restrictScalars A) :=
    Algebra.H1Cotangent.exact_map_δ Λ A k
  have hconj := (LinearEquiv.conj_symm_exact_iff_exact _ _ (cotangentEquivH1Cotangent h)).mpr hex
  rwa [δ_comp_cotangentEquivH1Cotangent h] at hconj

/-- **Stacks 06S7.** Let `Λ` be a ring, `k` a field and `A` a `Λ`-algebra with a `Λ`-algebra
surjection `A → k` with kernel `𝔪_A`. Then the four-term sequence

    H₁(L_{k/Λ}) ⟶ 𝔪_A/𝔪_A² ⟶ Ω_{A/Λ} ⊗_A k ⟶ Ω_{k/Λ} ⟶ 0

is exact: exact at `𝔪_A/𝔪_A²`, exact at `Ω_{A/Λ} ⊗_A k`, and surjective onto `Ω_{k/Λ}`. -/
@[stacks 06S7, ega "0 20.6.22" "last three terms"]
public theorem exact_cotangentSequence (h : Function.Surjective (algebraMap A k)) :
    Function.Exact (h1CotangentToCotangent Λ h)
        (KaehlerDifferential.kerCotangentToTensor Λ A k) ∧
      Function.Exact (KaehlerDifferential.kerCotangentToTensor Λ A k)
        (KaehlerDifferential.mapBaseChange Λ A k) ∧
      Function.Surjective (KaehlerDifferential.mapBaseChange Λ A k) :=
  ⟨exact_h1CotangentToCotangent h,
    KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange Λ A k h,
    KaehlerDifferential.mapBaseChange_surjective Λ A k h⟩

end Deformation

end
