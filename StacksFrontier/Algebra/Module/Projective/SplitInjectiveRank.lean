module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# A split injection of finite projective modules of the same rank is bijective

Let `R` be a commutative ring and `s : P →ₗ[R] Q` a linear map of finitely generated projective
`R`-modules which admits a linear retraction.  If `P` and `Q` have the same rank at every prime
of `R`, then `s` is bijective: the kernel of the retraction is a direct summand of `Q`,
complementary to the image of `s`, hence finitely generated projective of rank zero everywhere,
hence zero.

## Main results

* `Module.bijective_of_retraction_of_rankAtStalk_eq`.
-/

@[expose] public section

namespace Module

variable {R P Q : Type*} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup Q]
  [Module R Q]

/-- **A split injection of finite projective modules with the same rank at every prime is
bijective.** -/
theorem bijective_of_retraction_of_rankAtStalk_eq [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q] (s : P →ₗ[R] Q) (ρ : Q →ₗ[R] P)
    (hρ : ρ ∘ₗ s = LinearMap.id) (hrank : rankAtStalk (R := R) P = rankAtStalk (R := R) Q) :
    Function.Bijective s := by
  have hρs : ∀ p, ρ (s p) = p := fun p => LinearMap.congr_fun hρ p
  let K := LinearMap.ker ρ
  -- `Q ≅ P × K`
  let e : Q ≃ₗ[R] P × K :=
    { toFun := fun q => (ρ q, ⟨q - s (ρ q), by simp [K, hρs]⟩)
      invFun := fun pk => s pk.1 + pk.2
      map_add' := fun a b => by ext <;> simp; abel
      map_smul' := fun c a => by ext <;> simp [smul_sub]
      left_inv := fun q => by simp
      right_inv := fun pk => by
        obtain ⟨p, k, hk⟩ := pk
        have hk' : ρ k = 0 := hk
        ext <;> simp [hρs, hk'] }
  -- `K` is a direct summand of `Q`, hence finite and projective
  let πK : Q →ₗ[R] K := (LinearMap.snd R P K).comp e.toLinearMap
  let ιK : K →ₗ[R] Q := K.subtype
  have hπι : πK ∘ₗ ιK = LinearMap.id := by
    ext ⟨k, hk⟩
    have hk' : ρ k = 0 := hk
    simp [πK, ιK, e, hk']
  have hKfin : Module.Finite R K :=
    Module.Finite.of_surjective πK (fun k => ⟨ιK k, LinearMap.congr_fun hπι k⟩)
  have hKproj : Module.Projective R K := Module.Projective.of_split ιK πK hπι
  have hrk := rankAtStalk_prod (R := R) P K
  rw [← rankAtStalk_eq_of_equiv e, ← hrank] at hrk
  have hK0 : rankAtStalk (R := R) K = 0 := by
    funext p
    have := congrFun hrk p
    simp only [Pi.add_apply] at this
    simp only [Pi.zero_apply]
    omega
  have hKsub : Subsingleton K := (rankAtStalk_eq_zero_iff_subsingleton).1 hK0
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have : a - b ∈ K := by simp [K, hab]
    have h0 : (⟨a - b, this⟩ : K) = 0 := Subsingleton.elim _ _
    exact sub_eq_zero.1 (congrArg Subtype.val h0)
  refine ⟨fun a b hab => by simpa [hρs] using congrArg ρ hab, fun q => ⟨ρ q, ?_⟩⟩
  exact hρinj (hρs _)

end Module

end
