module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.EtaleStalkOrder

/-!
# Reading a local ring in the stalks of an étale scheme over its spectrum

Let `R` be a local ring and `σ : T ⟶ Spec R` an étale morphism of schemes, and let `t ∈ T` lie
over the closed point. The ring map `R → 𝒪_{T, t}`, `r ↦ (σ^♯ r)_t`, is the stalk map of `σ` at
`t` after the identification `R ≅ 𝒪_{Spec R, 𝔪}` of Mathlib's `stalkClosedPointIso`. It therefore
carries nonzerodivisors to nonzerodivisors and leaves the order of vanishing `Ring.ord`
unchanged (`AlgebraicGeometry.ord_stalkMap_of_etale`).

This is how the coefficient of a meromorphic section against the generator chosen at the
generic point of a prime divisor, which lives on `Spec(𝒪_{U, u})`, is read on an étale chart of
`Spec(𝒪_{U, u})`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.ringToStalk`: the map `R → 𝒪_{T, t}`.

## Main results

* `AlgebraicGeometry.bijective_germ_comp_ΓSpecIso_inv`: the germ at the closed point of `Spec R`
  is an isomorphism `R ≅ 𝒪_{Spec R, 𝔪}`.
* `AlgebraicGeometry.Scheme.Hom.ord_ringToStalk_of_etale` and
  `AlgebraicGeometry.Scheme.Hom.ringToStalk_mem_nonZeroDivisors_of_etale`.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped nonZeroDivisors

universe u

namespace Ring

/-- A bijective ring homomorphism between local rings leaves the order of vanishing unchanged. -/
theorem ord_map_of_bijective {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] {φ : A →+* B} (hφ : Function.Bijective φ) (x : A) :
    Ring.ord B (φ x) = Ring.ord A x := by
  have hloc : IsLocalHom φ := ⟨fun a ha => by
    have h := ha.map (RingEquiv.ofBijective φ hφ).symm
    rwa [show (RingEquiv.ofBijective φ hφ).symm (φ a) = a from
      (RingEquiv.ofBijective φ hφ).symm_apply_apply a] at h⟩
  exact ord_map_of_flat_of_map_maximalIdeal hloc (RingHom.Flat.of_bijective hφ)
    (map_maximalIdeal_of_surjective φ hφ.2) x

end Ring

namespace AlgebraicGeometry

/-- **The germ at the closed point of the spectrum of a local ring is an isomorphism**, read as
the ring map `R → 𝒪_{Spec R, x}` for any `x` equal to the closed point. -/
theorem bijective_germ_comp_ΓSpecIso_inv (R : CommRingCat.{u}) [IsLocalRing R] {x : Spec R}
    (hx : x = closedPoint R) :
    Function.Bijective (((Spec R).presheaf.germ ⊤ x trivial).hom.comp
      (Scheme.ΓSpecIso R).inv.hom) := by
  subst hx
  have e : ((Spec R).presheaf.germ ⊤ (closedPoint R) trivial).hom.comp
      (Scheme.ΓSpecIso R).inv.hom = (stalkClosedPointIso R).inv.hom := by
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    ext r
    simp
  rw [e]
  exact (stalkClosedPointIso R).symm.commRingCatIsoToRingEquiv.bijective

variable {T : Scheme.{u}} {R : CommRingCat.{u}} (σ : T ⟶ Spec R) (t : T)

/-- The ring map `R → 𝒪_{T, t}` along a morphism `σ : T ⟶ Spec R`: pull back along `σ` and take
the germ at `t`. -/
def Scheme.Hom.ringToStalk : R →+* T.presheaf.stalk t :=
  (T.presheaf.germ ⊤ t trivial).hom.comp (σ.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)

/-- The ring map `R → 𝒪_{T, t}` is the stalk map of `σ` at `t` after the germ at `σ(t)`. -/
theorem Scheme.Hom.ringToStalk_eq (r : R) :
    σ.ringToStalk t r = (σ.stalkMap t).hom
      (((Spec R).presheaf.germ ⊤ (σ.base t) trivial).hom ((Scheme.ΓSpecIso R).inv.hom r)) :=
  (Scheme.Hom.germ_stalkMap_apply σ ⊤ t trivial _).symm

variable [IsLocalRing R]

/-- **Along an étale morphism to the spectrum of a local ring, the ring map to the stalk at a
point over the closed point leaves the order of vanishing unchanged.** -/
theorem Scheme.Hom.ord_ringToStalk_of_etale [Etale σ] (ht : σ.base t = closedPoint R) (r : R) :
    Ring.ord (T.presheaf.stalk t) (σ.ringToStalk t r) = Ring.ord R r := by
  rw [σ.ringToStalk_eq t r, ord_stalkMap_of_etale]
  exact Ring.ord_map_of_bijective (bijective_germ_comp_ΓSpecIso_inv R ht) r

/-- **Along an étale morphism to the spectrum of a local ring, the ring map to the stalk at a
point over the closed point carries nonzerodivisors to nonzerodivisors.** -/
theorem Scheme.Hom.ringToStalk_mem_nonZeroDivisors_of_etale [Etale σ]
    (ht : σ.base t = closedPoint R) {r : R} (hr : r ∈ R⁰) :
    σ.ringToStalk t r ∈ (T.presheaf.stalk t)⁰ := by
  rw [σ.ringToStalk_eq t r]
  exact stalkMap_mem_nonZeroDivisors_of_flat σ t
    (Ring.map_mem_nonZeroDivisors_of_flatHom
      (RingHom.Flat.of_bijective (bijective_germ_comp_ΓSpecIso_inv R ht)) hr)

end AlgebraicGeometry

end
