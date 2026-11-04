module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.Deformation.BaseCategory.CotangentHomology
public import StacksFrontier.Deformation.TangentSpace.Derivations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tangent space of a prorepresentable functor is the relative tangent space

Let `Λ` be a Noetherian complete local ring with residue field `k'`, let `k/k'` be separable —
for instance `k = k'`, the classical case — and let `S` be an object of `\widehat{𝒞_Λ}` with
residue field `k`. The computation of Stacks 06IC then simplifies: the tangent space of the
functor `F = underline S|_{𝒞_Λ}` is the relative tangent space of `S` over `Λ`, that is the
`k`-linear dual of the relative cotangent space `𝔪_S / (𝔪_Λ S + 𝔪_S²)`:

    TF = T_{S/Λ} = (𝔪_S / (𝔪_Λ S + 𝔪_S²))^*.

## Main results

* `Deformation.existsUnique_derivationRelativeCotangentDualEquiv`: **Stacks 06SS**, the
  `Λ`-derivations `S → k` are the `k`-linear dual of the relative cotangent space, by the
  unique `k`-linear equivalence sending a derivation to its restriction to `𝔪_S`.
* `Deformation.existsUnique_tangentSpaceRelativeCotangentDualEquiv`: **Stacks 06SS**, the same
  statement read on the tangent space itself, through the identification of Stacks 06IC.
* `Deformation.existsUnique_tangentSpaceRelativeCotangentDualEquiv_of_isClassical`:
  **Stacks 06SS**, the classical case, where separability is automatic.

## Implementation notes

The relative cotangent space is `Deformation.relativeCotangentSpace`, with the residue-field
action of Stacks 06GY transported to `k` along the object's chosen residue-field
identification; this is the `Module k` instance installed by the `letI` prefix of each
statement, and it is what makes the dual a `k`-vector space.

The tangent space carries the canonical `k`-vector-space structure that Stacks 06IC installs
on the value of a prorepresentable functor at the dual numbers,
`Deformation.tangentSpaceModule`, obtained by transport along
`Deformation.tangentSpaceDerivationsLinearEquiv`. So the content of this file is the
identification of `Der_Λ(S, k)` with the dual, and the tangent-space form is the composite
with that equivalence; by `Deformation.tangentSpaceDerivationsLinearEquiv_apply` its
characterization reads off the square-zero coordinate of the image of an element of `𝔪_S`,
which is the form in which the source states it.

The mathematical step is the Jacobi–Zariski sequence for `Λ → S → k`. Its degree-one part
identifies `𝔪_S / (𝔪_Λ S + 𝔪_S²)` with `k ⊗_S Ω_{S/Λ}`: the conormal module `𝔪_S/𝔪_S²` is
`H₁(L_{k/S})` by Stacks 06S9, the connecting map lands in `k ⊗_S Ω_{S/Λ}`, its kernel is the
image of `H₁(L_{k/Λ})`, and that image is the image of `𝔪_Λ/𝔪_Λ²` precisely because the base
change of the canonical map of Stacks 06S9 is onto when `k/k'` is separable. Surjectivity onto
`k ⊗_S Ω_{S/Λ}` is the vanishing of `Ω_{k/Λ}`, which is formal unramifiedness of `Λ → k`,
itself the composite of the surjection `Λ → k'` with the separable extension `k/k'`. Dualizing
and using that a derivation is determined by its values on the maximal ideal gives the
statement.

## References

* [Stacks Project, Tag 06SS](https://stacks.math.columbia.edu/tag/06SS)
-/

@[expose] public section

open CategoryTheory KaehlerDifferential
open scoped TensorProduct

namespace Deformation

universe u v w

/-- A product of two elements of `J` lies in `I·A + J²`. -/
private theorem mul_mem_map_add_pow_two {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) {J : Ideal A} {a b : A} (ha : a ∈ J) (hb : b ∈ J) :
    a * b ∈ I.map (algebraMap R A) + J ^ 2 :=
  Submodule.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)

/-- The class in `H₁(L_{k/A})` of an element of `𝔪_A` has connecting image the corresponding
pure tensor `1 ⊗ d a` in `k ⊗_A Ω_{A/R}`. This is the degree-one part of the Jacobi–Zariski
sequence of `R → A → k`, read through the canonical map of Stacks 06S9. -/
private theorem conormalToH1Cotangent_delta
    {R A K : Type*} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    (h : Function.Surjective (algebraMap A K))
    (a : RingHom.ker (algebraMap A K)) :
    Algebra.H1Cotangent.δ R A K
      (conormalToH1Cotangent (Λ := A) (S := K) (k := K) h
        ((RingHom.ker (algebraMap A K)).toCotangent a)) =
      1 ⊗ₜ[A] D R A a := by
  have hmap : Algebra.H1Cotangent.map A A K K = LinearMap.id :=
    (Algebra.Extension.H1Cotangent.map_eq _ (.id _)).trans
      Algebra.Extension.H1Cotangent.map_id
  simp only [conormalToH1Cotangent, hmap, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.id_apply]
  unfold conormalToH1CotangentOfSurjective
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  apply Algebra.Generators.H1Cotangent.δ_C

/-- The relative cotangent quotient `J / (I·A + J²)` of a surjection `A → K` relative to a
surjection `R → k` with `K/k` separable is `K ⊗_A Ω_{A/R}`, by the pure-tensor rule. This is
the degree-one Jacobi–Zariski sequence of `R → A → K`: exactness on the left comes from the
separable base-change isomorphism of Stacks 06S9, and surjectivity on the right from the
vanishing of `Ω_{K/R}`. -/
private theorem exists_conormalQuotientEquiv
    (R A k K : Type*) [CommRing R] [CommRing A] [Field k] [Field K]
    [Algebra R A] [Algebra R k] [Algebra R K] [Algebra A K] [Algebra k K]
    [IsScalarTower R A K] [IsScalarTower R k K]
    (hR : Function.Surjective (algebraMap R k))
    (hA : Function.Surjective (algebraMap A K)) [Algebra.IsSeparable k K]
    (I : Ideal R) (J : Ideal A)
    (hI : I = RingHom.ker (algebraMap R k))
    (hJ : J = RingHom.ker (algebraMap A K)) :
    let P := Submodule.comap J.subtype (I.map (algebraMap R A) + J ^ 2)
    ∃ e : (J ⧸ P) ≃ₗ[A] K ⊗[A] Ω[A⁄R],
      ∀ a : J, e (Submodule.Quotient.mk a) = 1 ⊗ₜ[A] D R A a := by
  subst hI hJ
  let I := RingHom.ker (algebraMap R k)
  let J := RingHom.ker (algebraMap A K)
  let P := Submodule.comap J.subtype (I.map (algebraMap R A) + J ^ 2)
  let d : J →ₗ[A] K ⊗[A] Ω[A⁄R] := kerToTensor R A K
  have hd (a : J) : d a = 1 ⊗ₜ[A] D R A a := rfl
  have hIP : I.map (algebraMap R A) ≤ d.ker.map J.subtype := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    refine ⟨⟨algebraMap R A r,
      ker_algebraMap_le_comap_ker (Λ := R) (S := k) (k := K) hr⟩, ?_, rfl⟩
    change d _ = 0
    simp [hd]
  have hJP : J ^ 2 ≤ d.ker.map J.subtype := by
    intro a ha
    have haj : a ∈ J := (Ideal.pow_le_self two_ne_zero) ha
    refine ⟨⟨a, haj⟩, ?_, rfl⟩
    change d _ = 0
    rw [show d ⟨a, haj⟩ = kerCotangentToTensor R A K (J.toCotangent ⟨a, haj⟩) from rfl,
      (J.toCotangent_eq_zero _).mpr ha, map_zero]
  have hP : P ≤ d.ker := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := (show I.map (algebraMap R A) + J ^ 2 ≤ d.ker.map J.subtype from
      sup_le hIP hJP) ha
    exact (Subtype.ext hba : b = a) ▸ hb
  let l : J ⧸ P →ₗ[A] K ⊗[A] Ω[A⁄R] := P.liftQ d hP
  let c : J.Cotangent ≃ₗ[A] Algebra.H1Cotangent A K :=
    LinearEquiv.ofBijective
      (conormalToH1Cotangent (Λ := A) (S := K) (k := K) hA)
      (conormalToH1Cotangent_bijective_of_surjective hA)
  let q : J.Cotangent →ₗ[A] J ⧸ P := Ideal.Cotangent.lift P.mkQ (by
    intro a b
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    exact mul_mem_map_add_pow_two I a.2 b.2)
  have hq (a : J) : q (J.toCotangent a) = Submodule.Quotient.mk a := rfl
  have hc (a : J) : Algebra.H1Cotangent.δ R A K (c (J.toCotangent a)) = d a :=
    conormalToH1Cotangent_delta hA a
  have hl (z : J.Cotangent) : l (q z) = Algebra.H1Cotangent.δ R A K (c z) := by
    obtain ⟨a, rfl⟩ := J.toCotangent_surjective z
    exact (hc a).symm
  let p : Algebra.H1Cotangent A K →ₗ[A] J ⧸ P := q ∘ₗ c.symm.toLinearMap
  have hle : I ≤ J.comap (algebraMap R A) :=
    ker_algebraMap_le_comap_ker (Λ := R) (S := k) (k := K) (A := A)
  have hpbase (z : I.Cotangent) :
      p (Algebra.H1Cotangent.map R A K K
        (conormalToH1Cotangent (Λ := R) (S := k) (k := K) hR z)) = 0 := by
    obtain ⟨r, rfl⟩ := I.toCotangent_surjective z
    have hstep : Algebra.H1Cotangent.map R A K K
        (conormalToH1Cotangent (Λ := R) (S := k) (k := K) hR (I.toCotangent r)) =
        c (J.toCotangent ⟨algebraMap R A r, hle r.2⟩) := by
      rw [conormalToH1Cotangent_comp hR hA]
      rfl
    change q (c.symm _) = 0
    rw [hstep, c.symm_apply_apply, hq]
    exact (Submodule.Quotient.mk_eq_zero P).mpr
      ((show I.map (algebraMap R A) ≤ I.map (algebraMap R A) + J ^ 2 from le_sup_left)
        (Ideal.mem_map_of_mem _ r.2))
  have hpzero (z : Algebra.H1Cotangent R K) :
      p (Algebra.H1Cotangent.map R A K K z) = 0 := by
    obtain ⟨t, rfl⟩ :=
      (conormalToH1Cotangent_baseChange_bijective
        (Λ := R) (S := k) (k := K) hR).surjective z
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul b y =>
      obtain ⟨a, rfl⟩ := hA b
      rw [LinearMap.liftBaseChange_tmul, map_smul,
        IsScalarTower.algebraMap_smul K a, p.map_smul, hpbase, smul_zero]
  have hinj : Function.Injective l := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := P.mkQ_surjective z
    obtain ⟨b, hb⟩ := (Algebra.H1Cotangent.exact_map_δ R A K _).mp ((hc a).trans hz)
    have hp := hpzero b
    rw [hb] at hp
    simpa [p, hq] using hp
  have hsurj : Function.Surjective l := by
    have : Algebra.FormallyUnramified R k :=
      Algebra.FormallyUnramified.of_surjective (Algebra.ofId R k) hR
    have : Algebra.FormallyUnramified k K := Algebra.FormallyUnramified.of_isSeparable k K
    have : Algebra.FormallyUnramified R K := Algebra.FormallyUnramified.comp R k K
    intro z
    obtain ⟨b, hb⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A K z).mp
      (Subsingleton.elim _ _)
    refine ⟨q (c.symm b), ?_⟩
    rw [hl, c.apply_symm_apply, hb]
  exact ⟨LinearEquiv.ofBijective l ⟨hinj, hsurj⟩, fun a => rfl⟩

/-- For local rings, the relative cotangent space of `R → A` is `K ⊗_A Ω_{A/R}`, `K` being the
residue field of `A` and separable over the residue field of `R`. The equivalence is `K`-linear
because `A → K` is onto. -/
private theorem exists_localCotangentEquiv
    (R A k K : Type*) [CommRing R] [CommRing A] [Field k] [Field K]
    [IsLocalRing R] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Algebra R k] [Algebra R K] [Algebra A K] [Algebra k K]
    [IsScalarTower R A K] [IsScalarTower R k K] [Algebra.IsSeparable k K]
    (hR : Function.Surjective (algebraMap R k))
    (hA : Function.Surjective (algebraMap A K))
    [Module K (relativeCotangentSpace (algebraMap R A))]
    [IsScalarTower A K (relativeCotangentSpace (algebraMap R A))] :
    ∃ e : relativeCotangentSpace (algebraMap R A) ≃ₗ[K] K ⊗[A] Ω[A⁄R],
      ∀ a : IsLocalRing.maximalIdeal A,
        e (Submodule.Quotient.mk a) = 1 ⊗ₜ[A] D R A a := by
  have hI := (IsLocalRing.ker_eq_maximalIdeal (algebraMap R k) hR).symm
  have hJ := (IsLocalRing.ker_eq_maximalIdeal (algebraMap A K) hA).symm
  obtain ⟨e, he⟩ := exists_conormalQuotientEquiv R A k K hR hA
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal A) hI hJ
  let e' : relativeCotangentSpace (algebraMap R A) ≃ₗ[A] K ⊗[A] Ω[A⁄R] := by
    simpa [relativeCotangentSpace, hI, hJ] using e
  exact ⟨e'.extendScalarsOfSurjective hA, he⟩

/-- Dualizing the identification of the relative cotangent space with `K ⊗_A Ω_{A/R}`: a
`Λ`-derivation into the residue field is a functional on the relative cotangent space. -/
private noncomputable def derivationToRelativeCotangentDual
    {R A K : Type*} [CommRing R] [CommRing A] [Field K]
    [IsLocalRing R] [IsLocalRing A]
    [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    [IsLocalHom (algebraMap R A)]
    [AddCommGroup (relativeCotangentSpace (algebraMap R A))]
    [Module A (relativeCotangentSpace (algebraMap R A))]
    [Module K (relativeCotangentSpace (algebraMap R A))]
    [IsScalarTower A K (relativeCotangentSpace (algebraMap R A))]
    (hAK : Function.Surjective (algebraMap A K))
    (e : relativeCotangentSpace (algebraMap R A) ≃ₗ[K] K ⊗[A] Ω[A⁄R]) :
    Derivation R A K ≃ₗ[K] (relativeCotangentSpace (algebraMap R A) →ₗ[K] K) :=
  let d := LinearEquiv.extendScalarsOfSurjective hAK
    (KaehlerDifferential.linearMapEquivDerivation R A (M := K))
  let l := LinearMap.liftBaseChangeEquiv (R := A) (M := Ω[A⁄R]) (N := K) K
  d.symm.trans (l.trans e.dualMap)

/-- The dual functional attached to a derivation is the derivation itself on the maximal
ideal. -/
private theorem derivationToRelativeCotangentDual_apply
    {R A K : Type*} [CommRing R] [CommRing A] [Field K]
    [IsLocalRing R] [IsLocalRing A]
    [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    [IsLocalHom (algebraMap R A)]
    [AddCommGroup (relativeCotangentSpace (algebraMap R A))]
    [Module A (relativeCotangentSpace (algebraMap R A))]
    [Module K (relativeCotangentSpace (algebraMap R A))]
    [IsScalarTower A K (relativeCotangentSpace (algebraMap R A))]
    (hAK : Function.Surjective (algebraMap A K))
    (e : relativeCotangentSpace (algebraMap R A) ≃ₗ[K] K ⊗[A] Ω[A⁄R])
    (he : ∀ a : IsLocalRing.maximalIdeal A,
      e (Submodule.Quotient.mk a) = 1 ⊗ₜ[A] D R A a)
    (D : Derivation R A K) (a : IsLocalRing.maximalIdeal A) :
    derivationToRelativeCotangentDual hAK e D (Submodule.Quotient.mk a) = D a := by
  simp only [derivationToRelativeCotangentDual, LinearEquiv.trans_apply,
    LinearEquiv.dualMap_apply, he]
  erw [LinearMap.liftBaseChange_one_tmul]
  exact D.liftKaehlerDifferential_comp_D a

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks 06SS.** For a base `Λ` whose residue field `k₀` has `k` separable over it, the
`Λ`-derivations from an object `S` of `\widehat{𝒞_Λ}` to `k` are the `k`-linear dual of the
relative cotangent space of `S` over `Λ`, by the unique `k`-linear equivalence that restricts
a derivation to the maximal ideal of `S`. -/
@[stacks 06SS "derivations are the dual of the relative cotangent space",
  sga "3 VIIA 1.3.1" "special case"]
theorem existsUnique_derivationRelativeCotangentDualEquiv
    {k₀ : Type*} [Field k₀] [Algebra Λ k₀] [Algebra k₀ k] [IsScalarTower Λ k₀ k]
    [IsLocalRing Λ] [Algebra.IsSeparable k₀ k]
    (hbase : Function.Surjective (algebraMap Λ k₀))
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    ∃ hlocal : IsLocalHom (algebraMap Λ S),
      letI := hlocal
      letI : Module k (relativeCotangentSpace (algebraMap Λ S)) :=
        Module.compHom _ S.residueEquiv.symm.toRingHom
      letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
      ∃! e : Derivation Λ S k ≃ₗ[k]
          (relativeCotangentSpace (algebraMap Λ S) →ₗ[k] k),
        ∀ (D : Derivation Λ S k) (x : IsLocalRing.maximalIdeal S),
          e D (Submodule.Quotient.mk x) = D (x : S) := by
  let rho := residueHom S
  let : Algebra S k := rho.toRingHom.toAlgebra
  have : IsScalarTower Λ S k := IsScalarTower.of_algebraMap_smul fun r x => by
    simp only [Algebra.smul_def]
    change rho (algebraMap Λ S r) * x = algebraMap Λ k r * x
    exact congrArg (fun z : k => z * x) (rho.commutes r)
  have hS : Function.Surjective (algebraMap S k) :=
    S.residueEquiv.surjective.comp IsLocalRing.residue_surjective
  have : IsLocalHom (algebraMap S k) := hS.isLocalHom
  have : IsLocalHom (algebraMap Λ k₀) := hbase.isLocalHom
  have hlocalBase : IsLocalHom (algebraMap Λ k) := by
    rw [IsScalarTower.algebraMap_eq Λ k₀ k]
    exact RingHom.isLocalHom_comp _ _
  have hcompS : (algebraMap S k).comp (algebraMap Λ S) = algebraMap Λ k := by
    ext x
    exact rho.commutes x
  have hlocal : IsLocalHom (algebraMap Λ S) := by
    have : IsLocalHom ((algebraMap S k).comp (algebraMap Λ S)) := hcompS ▸ hlocalBase
    exact isLocalHom_of_comp (algebraMap Λ S) (algebraMap S k)
  let : Module k (relativeCotangentSpace (algebraMap Λ S)) :=
    Module.compHom _ S.residueEquiv.symm.toRingHom
  have hTorsion : Module.IsTorsionBySet S
      (relativeCotangentSpace (algebraMap Λ S))
      (IsLocalRing.maximalIdeal S : Set S) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro x r hr
    exact mul_mem_map_add_pow_two (IsLocalRing.maximalIdeal Λ) hr x.2
  have : IsScalarTower S (IsLocalRing.ResidueField S)
      (relativeCotangentSpace (algebraMap Λ S)) := hTorsion.isScalarTower
  have hscalar (s : S) :
      S.residueEquiv.symm.toRingHom (algebraMap S k s) =
        algebraMap S (IsLocalRing.ResidueField S) s :=
    S.residueEquiv.symm_apply_apply _
  have : IsScalarTower S k (relativeCotangentSpace (algebraMap Λ S)) :=
    IsScalarTower.of_algebraMap_smul fun s y => by
      change S.residueEquiv.symm.toRingHom (algebraMap S k s) • y = s • y
      rw [hscalar]
      exact (IsScalarTower.algebraMap_smul (A := IsLocalRing.ResidueField S) s y).symm
  obtain ⟨eCot, heCot⟩ := exists_localCotangentEquiv Λ S k₀ k hbase hS
  refine ⟨hlocal, derivationToRelativeCotangentDual hS eCot,
    derivationToRelativeCotangentDual_apply hS eCot heCot,
    fun e' he' => LinearEquiv.ext fun D => LinearMap.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (Submodule.comap (IsLocalRing.maximalIdeal S).subtype
      ((IsLocalRing.maximalIdeal Λ).map (algebraMap Λ S) +
        IsLocalRing.maximalIdeal S ^ 2)) y
  exact (he' D x).trans
    (derivationToRelativeCotangentDual_apply hS eCot heCot D x).symm

/-- **Stacks 06SS.** The tangent space of the functor prorepresented by `S` is the relative
tangent space of `S` over `Λ`, that is the `k`-linear dual of the relative cotangent space.
The equivalence is characterized by taking the coefficient of the square-zero coordinate of
the image of an element of the maximal ideal, and is unique with that property. -/
@[stacks 06SS "the tangent space is the relative tangent space"]
theorem existsUnique_tangentSpaceRelativeCotangentDualEquiv
    {k₀ : Type*} [Field k₀] [Algebra Λ k₀] [Algebra k₀ k] [IsScalarTower Λ k₀ k]
    [IsLocalRing Λ] [Algebra.IsSeparable k₀ k]
    (hbase : Function.Surjective (algebraMap Λ k₀))
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    ∃ hlocal : IsLocalHom (algebraMap Λ S),
      letI := hlocal
      letI : Module k (relativeCotangentSpace (algebraMap Λ S)) :=
        Module.compHom _ S.residueEquiv.symm.toRingHom
      ∃! e : tangentSpaceArtinian Λ k (restrictedCoyoneda S) ≃ₗ[k]
          (relativeCotangentSpace (algebraMap Λ S) →ₗ[k] k),
        ∀ (t : tangentSpaceArtinian Λ k (restrictedCoyoneda S))
          (x : IsLocalRing.maximalIdeal S),
          e t (Submodule.Quotient.mk x) = (t.hom (x : S)).snd.down := by
  obtain ⟨hlocal, e, he, huniq⟩ :=
    existsUnique_derivationRelativeCotangentDualEquiv (k₀ := k₀) hbase S
  refine ⟨hlocal, (tangentSpaceDerivationsLinearEquiv S).trans e,
    fun t x => (he _ x).trans (tangentSpaceDerivationsLinearEquiv_apply S t (x : S)), ?_⟩
  intro e' he'
  have h : (tangentSpaceDerivationsLinearEquiv S).symm.trans e' = e := by
    refine huniq _ fun D x => ?_
    change e' ((tangentSpaceDerivationsLinearEquiv S).symm D) _ = _
    rw [he']
    have := tangentSpaceDerivationsLinearEquiv_apply S
      ((tangentSpaceDerivationsLinearEquiv S).symm D) (x : S)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  rw [← h]
  exact LinearEquiv.ext fun t => by simp

/-- **Stacks 06SS.** The classical case: when `Λ` is a Noetherian complete local ring with
residue field `k`, the tangent space of the functor prorepresented by `S` is the `k`-linear
dual of the relative cotangent space of `S` over `Λ`. Separability is automatic here, the
residue extension being trivial. -/
@[stacks 06SS "classical case"]
theorem existsUnique_tangentSpaceRelativeCotangentDualEquiv_of_isClassical
    (hΛ : IsClassical Λ k) (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    letI : IsLocalRing Λ := (Classical.choose hΛ).isLocal
    ∃ hlocal : IsLocalHom (algebraMap Λ S),
      letI := hlocal
      letI : Module k (relativeCotangentSpace (algebraMap Λ S)) :=
        Module.compHom _ S.residueEquiv.symm.toRingHom
      ∃! e : tangentSpaceArtinian Λ k (restrictedCoyoneda S) ≃ₗ[k]
          (relativeCotangentSpace (algebraMap Λ S) →ₗ[k] k),
        ∀ (t : tangentSpaceArtinian Λ k (restrictedCoyoneda S))
          (x : IsLocalRing.maximalIdeal S),
          e t (Submodule.Quotient.mk x) = (t.hom (x : S)).snd.down := by
  let : IsLocalRing Λ := (Classical.choose hΛ).isLocal
  obtain ⟨eRes⟩ := Classical.choose_spec hΛ
  have hbase : Function.Surjective (algebraMap Λ k) := by
    intro y
    obtain ⟨z, hz⟩ := eRes.surjective y
    obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective z
    refine ⟨x, ?_⟩
    calc
      algebraMap Λ k x = eRes (algebraMap Λ (IsLocalRing.ResidueField Λ) x) :=
        (AlgEquiv.commutes eRes x).symm
      _ = eRes (IsLocalRing.residue Λ x) := by
        rw [IsLocalRing.ResidueField.algebraMap_eq]
      _ = y := by rwa [hx]
  exact existsUnique_tangentSpaceRelativeCotangentDualEquiv (k₀ := k) hbase S

end Deformation

end
