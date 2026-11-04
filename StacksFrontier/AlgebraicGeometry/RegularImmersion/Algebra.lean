module

public import StacksFrontier.RingTheory.Koszul.FlatQuotient

/-!
# Relative quasi-regular sequences are regular on the stalks

Let `R → S` be flat and of finite presentation, let `f₁, …, f_r ∈ S` be a quasi-regular
sequence, and assume the quotient `S/(f₁, …, f_r)` is flat over `R`.  Then for every prime
`Q ⊆ S` containing the `fᵢ` the sequence `f₁, …, f_r` is a *regular* sequence in the
localization `S_Q`, and each partial quotient `S_Q/(f₁, …, f_i)` is flat over `R`. Let
`p = Q ∩ R`.

## Main results

* `Stacks.RingTheory.RelativeQuasiRegular.isRegular_fibre`: the image of the sequence in the
  closed fibre `S_Q/pS_Q` is a regular sequence.
* `Stacks.RingTheory.RelativeQuasiRegular.isRegular_localization_and_flat_quotients`: the
  sequence is regular in `S_Q` and every partial quotient is `R`-flat.

## References

* [Stacks Project, Tag 063U](https://stacks.math.columbia.edu/tag/063U)
* [Stacks Project, Tag 0CEP](https://stacks.math.columbia.edu/tag/0CEP)
* [Stacks Project, Tag 061S](https://stacks.math.columbia.edu/tag/061S)
* [Stacks Project, Tag 0470](https://stacks.math.columbia.edu/tag/0470)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.RingTheory.RelativeQuasiRegular

open RingTheory.Sequence

universe u v

/-- A quasi-regular sequence in `S` whose quotient is flat over `R` has regular image in the
closed fibre of a local `R`-algebra `T` over a localization `P` of `R`. -/
public theorem isRegular_fibre
    {R S P T : Type*} [CommRing R] [CommRing S] [CommRing P] [CommRing T]
    [Algebra R S] [Algebra R P] [Algebra R T] [Algebra P T] [Algebra S T]
    [IsScalarTower R S T] [IsScalarTower R P T]
    [IsLocalRing P] [IsLocalRing T] [IsLocalHom (algebraMap P T)]
    [Module.Flat S T] [Algebra.EssFiniteType R T]
    (U : Submonoid R) [IsLocalization U P]
    {r : ℕ} (f : Fin r → S)
    (hf : ∀ i, algebraMap S T (f i) ∈ IsLocalRing.maximalIdeal T)
    (hqr : IsQuasiRegular S (List.ofFn f))
    (hflat : Module.Flat R (S ⧸ Ideal.span (Set.range f))) :
    IsRegular (T ⧸ (IsLocalRing.maximalIdeal P).map (algebraMap P T))
      (List.ofFn fun i ↦ algebraMap S T (f i)) := by
  let m := IsLocalRing.maximalIdeal P
  let K := P ⧸ m
  let D := T ⧸ m.map (algebraMap P T)
  let : Field K := Ideal.Quotient.field m
  have h0 : IsQuasiRegular (S ⊗[R] K) (List.ofFn (KoszulH1.fp (A := R) (A' := K) f)) :=
    (Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat (A := R) (A' := K) f hflat).1
      hqr
  let e₁ : (S ⊗[R] K) ≃ₐ[R] (K ⊗[R] S) := Algebra.TensorProduct.comm R S K
  have h1 := Koszul.isQuasiRegular_map_of_flat e₁.toRingHom
    (RingHom.Flat.of_bijective e₁.bijective) h0
  let g : K ⊗[R] S →ₐ[K] K ⊗[R] T :=
    Algebra.TensorProduct.lTensor K (IsScalarTower.toAlgHom R S T)
  have hg : g.Flat := (show (IsScalarTower.toAlgHom R S T).Flat from
    (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat S T›)).lTensor K
  have h2 := Koszul.isQuasiRegular_map_of_flat g.toRingHom hg h1
  have h2' : IsQuasiRegular (K ⊗[R] T)
      (List.ofFn fun i ↦ (1 : K) ⊗ₜ[R] algebraMap S T (f i)) := by
    simpa [List.map_ofFn, Function.comp_def, KoszulH1.fp, KoszulH1.inclLeft, e₁, g] using h2
  let e₂ := Koszul.localizationFiberEquiv (T := T) U m
  have h3 := Koszul.isQuasiRegular_map_of_flat e₂.symm.toRingHom
    (RingHom.Flat.of_bijective e₂.symm.bijective) h2'
  have hqrD : IsQuasiRegular D
      (List.ofFn fun i ↦
        Ideal.Quotient.mk (m.map (algebraMap P T)) (algebraMap S T (f i))) := by
    rw [List.map_ofFn] at h3
    change IsQuasiRegular D
      (List.ofFn fun i ↦ e₂.symm ((1 : K) ⊗ₜ[R] algebraMap S T (f i))) at h3
    simpa only [e₂, Koszul.localizationFiberEquiv_symm_tmul_one] using h3
  have : IsNoetherianRing (K ⊗[R] T) := Algebra.EssFiniteType.isNoetherianRing K _
  have : IsNoetherianRing D := isNoetherianRing_of_ringEquiv _ e₂.symm
  have : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr
    (IsLocalRing.map_maximalIdeal_lt_top (algebraMap P T)).ne
  have : IsLocalRing D := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (m.map (algebraMap P T))) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (m.map (algebraMap P T))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmem : ∀ i, Ideal.Quotient.mk (m.map (algebraMap P T))
      (algebraMap S T (f i)) ∈ IsLocalRing.maximalIdeal D := fun i ↦
    IsLocalRing.map_maximalIdeal_le (Ideal.Quotient.mk (m.map (algebraMap P T)))
      (Ideal.mem_map_of_mem _ (hf i))
  have hreg := ((Koszul.regular_koszulRegular_h1Regular_quasiRegular_tfae
    (M := D) _ hmem).2.out 4 1).mp hqrD
  have hc := (AddEquiv.refl D).isRegular_congr (R := T) (S := D)
    (as := List.ofFn fun i ↦ algebraMap S T (f i))
    (bs := (List.ofFn fun i ↦ algebraMap S T (f i)).map (algebraMap T D))
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun t _ x ↦ (algebraMap_smul D t x).symm)))
  exact hc.mpr (by rw [List.map_ofFn]; exact hreg)

/-- Let `R → S` be flat and of finite presentation, let `f₁, …, f_r ∈ S` be a quasi-regular
sequence whose quotient `S/(f₁, …, f_r)` is flat over `R`, and let `Q` be a prime of `S`
containing every `fᵢ`.  Then `f₁, …, f_r` is a *regular* sequence in `S_Q`, and every partial
quotient `S_Q/(f₁, …, f_i)` is flat over `R`. -/
public theorem isRegular_localization_and_flat_quotients
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    {r : ℕ} (f : Fin r → S)
    (hqr : IsQuasiRegular S (List.ofFn f))
    (hflat : Module.Flat R (S ⧸ Ideal.span (Set.range f)))
    (Q : Ideal S) [Q.IsPrime] (hf : ∀ i, f i ∈ Q) :
    IsRegular (Localization.AtPrime Q)
        (List.ofFn fun i ↦ algebraMap S (Localization.AtPrime Q) (f i)) ∧
      ∀ i : ℕ, Module.Flat R
        (Localization.AtPrime Q ⧸
          Ideal.ofList
            ((List.ofFn fun j ↦ algebraMap S (Localization.AtPrime Q) (f j)).take i)) := by
  classical
  let T := Localization.AtPrime Q
  let p := Q.comap (algebraMap R S)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver p := ⟨rfl⟩
  let P := Localization.AtPrime p
  let : Algebra P T := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsLocalHom (algebraMap P T) :=
    Localization.isLocalHom_localRingHom p Q (algebraMap R S) rfl
  have : Module.Flat P T :=
    (Module.flat_iff_of_isLocalization P p.primeCompl T).mpr inferInstance
  have hreg := isRegular_fibre (P := P) (T := T) p.primeCompl f
    (fun i ↦ (IsLocalization.AtPrime.to_map_mem_maximal_iff T Q (f i)).mpr (hf i)) hqr hflat
  have hess : (algebraMap P T).EssentiallyOfFinitePresentation :=
    Koszul.essentiallyOfFinitePresentation_localization (S := S) p.primeCompl Q.primeCompl
      (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  have he (J : Ideal T) : J • (⊤ : Submodule T T) = J :=
    (Ideal.smul_eq_mul J ⊤).trans (Ideal.mul_top J)
  have hreg' : IsRegular
      (T ⧸ ((IsLocalRing.maximalIdeal P).map (algebraMap P T) • (⊤ : Submodule T T)))
      (List.ofFn fun i ↦ algebraMap S T (f i)) := by
    rwa [he]
  obtain ⟨h1, h2⟩ := Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
    (R := P) (S := T) (M := T) hess _ hreg'
  refine ⟨h1, fun i ↦ ?_⟩
  have := h2 i
  rw [he] at this
  exact .trans R P _

end Stacks.RingTheory.RelativeQuasiRegular

end
