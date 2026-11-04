module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction

/-!
# The ideal of the reduction pulled back to an affine scheme

Let `X` be an fppf sheaf on the big fppf site of `S` with a reduction `i : X_red ⟶ X`. For an
affine object `T` of the site and a section `t ∈ X(T)`, the base change `T ×_X X_red ⟶ T` is a
closed immersion, cut out by an ideal `K(t)` of `Γ(T, 𝒪_T)`, characterized by the points it
cuts out: a morphism `h : T' ⟶ T` from an affine object has `X(h)(t)` in `X_red` exactly when `h`
kills `K(t)`. The infinitesimal neighbourhoods `X_n` of `X_red` in `X` (Stacks 0GHM) are defined
through this ideal.

## Main results

* `AlgebraicGeometry.Scheme.exists_factor_iff_ker_appTop_le`: a morphism into an affine scheme
  factors through a closed immersion exactly when it kills the ideal of the closed immersion.
* `AlgebraicGeometry.FormalSpace.IsReduction.exists_reductionIdeal`: the ideal `K(t)`.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A morphism `h : T' ⟶ T` into an affine scheme factors through a closed immersion `c : Z ⟶ T`
exactly when the kernel of `c` on global sections lies in the kernel of `h`. -/
theorem Scheme.exists_factor_iff_ker_appTop_le {Z T T' : Scheme.{u}} [IsAffine T]
    (c : Z ⟶ T) [IsClosedImmersion c] (h : T' ⟶ T) :
    (∃ l : T' ⟶ Z, l ≫ c = h) ↔ RingHom.ker c.appTop.hom ≤ RingHom.ker h.appTop.hom := by
  constructor
  · rintro ⟨l, rfl⟩ x hx
    simp only [RingHom.mem_ker, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply] at hx ⊢
    rw [hx, map_zero]
  · intro hle
    have hker : c.ker ≤ h.ker := by
      rw [Scheme.ker_of_isAffine c, Scheme.ker_of_isAffine h]
      exact (Scheme.IdealSheafData.equivOfIsAffine (X := T)).symm.toOrderIso.monotone hle
    exact ⟨IsClosedImmersion.lift c h hker, IsClosedImmersion.lift_fac c h hker⟩

namespace FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the underlying schemes of objects of the site over a morphism of the site
lifts to the site. -/
theorem exists_siteHom_of_toScheme_comp_eq {T' Z T : BigFppfOver B S hS} (c : Z ⟶ T)
    (h : T' ⟶ T)
    (l : (BigFppfOver.toScheme B S hS).obj T' ⟶ (BigFppfOver.toScheme B S hS).obj Z)
    (hl : l ≫ (BigFppfOver.toScheme B S hS).map c = (BigFppfOver.toScheme B S hS).map h) :
    ∃ l₀ : T' ⟶ Z, l₀ ≫ c = h := by
  have h₁ : B.inclusion.preimage l ≫ c.left = h.left :=
    B.inclusion.map_injective (by rw [B.inclusion.map_comp, B.inclusion.map_preimage]; exact hl)
  exact ⟨Over.homMk (B.inclusion.preimage l) (by rw [← Over.w c, ← Category.assoc, h₁, Over.w h]),
    Over.OverMorphism.ext h₁⟩

/-- Let `i : X_red ⟶ X` be a reduction of an fppf sheaf `X`, let `T` be an affine object of the
site and `t ∈ X(T)`. There is an ideal `K ⊆ Γ(T, 𝒪_T)` such that a morphism `h : T' ⟶ T` of the
site carries `t` into `X_red` exactly when `h` kills `K`: it is the ideal of the closed immersion
`T ×_X X_red ⟶ T`. -/
theorem IsReduction.exists_reductionIdeal {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hred : IsReduction B S hS X Xred i) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t : X.obj.obj (op T)) :
    ∃ K : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤),
      ∀ (T' : BigFppfOver B S hS) (h : T' ⟶ T),
        (∃ r : Xred.obj.obj (op T'), i.hom.app (op T') r = X.obj.map h.op t) ↔
          K ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map h).appTop.hom := by
  classical
  let g : uliftYoneda.{u + 1}.obj T ⟶ X.obj := uliftYonedaEquiv.symm t
  obtain ⟨b, snd, fst, hsq⟩ := hred.representable g
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd) :=
    (hred.thickening g fst snd hsq).1
  refine ⟨RingHom.ker ((BigFppfOver.toScheme B S hS).map snd).appTop.hom, fun T' h => ?_⟩
  rw [← Scheme.exists_factor_iff_ker_appTop_le]
  have hgh : uliftYoneda.map h ≫ g = uliftYonedaEquiv.symm (X.obj.map h.op t) := by
    rw [uliftYonedaEquiv_symm_map]
    rfl
  constructor
  · rintro ⟨r, hr⟩
    have hw : uliftYonedaEquiv.symm r ≫ i.hom = uliftYoneda.map h ≫ g := by
      rw [uliftYonedaEquiv_symm_comp, hr, hgh]
    obtain ⟨l, -, hl⟩ := hsq.exists_lift _ _ hw
    obtain ⟨l₀, rfl⟩ : ∃ l₀ : T' ⟶ b, uliftYoneda.map l₀ = l :=
      ⟨uliftYoneda.preimage l, uliftYoneda.map_preimage l⟩
    refine ⟨(BigFppfOver.toScheme B S hS).map l₀, ?_⟩
    rw [← Functor.map_comp]
    exact congrArg _ (uliftYoneda.map_injective (by rw [Functor.map_comp]; exact hl))
  · rintro ⟨l, hl⟩
    obtain ⟨l₀, hl₀⟩ := exists_siteHom_of_toScheme_comp_eq snd h l hl
    refine ⟨fst.app (op T') (uliftYonedaEquiv (uliftYoneda.map l₀)), ?_⟩
    have := congrArg (fun φ => uliftYonedaEquiv (uliftYoneda.map l₀ ≫ φ)) hsq.w
    simp only [uliftYonedaEquiv_comp] at this
    refine this.trans ?_
    rw [← uliftYonedaEquiv_comp, ← Category.assoc, ← Functor.map_comp, hl₀, hgh,
      Equiv.apply_symm_apply]

end FormalSpace

end AlgebraicGeometry

end
