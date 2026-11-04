module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.RingTheory.C1573Port.Descent.EqualizerNilpotentLift

namespace CommRingCat.C1573
end CommRingCat.C1573
namespace AlgebraicGeometry.C1573
end AlgebraicGeometry.C1573

/-!
# Lifting a regular function along a nilpotent thickening of an affine Čech nerve

Let `U' → X'` be an affine étale chart of an algebraic space, with double and triple overlaps
`R' = U' ×_{X'} U'` and `R'' = R' ×_{U'} R'`, all affine, and let `X ⊂ X'` be a closed subspace
which is an affine scheme `T`, cut out on `U'` by a closed subscheme `U` whose ideal is
nilpotent. This file proves, in terms of the affine schemes alone, that every regular function
on `T`, pulled back to `U`, is the restriction of a regular function on `U'` whose two pullbacks
to `R'` agree.

The only input about the algebraic spaces is a list of cartesian squares of affine schemes; the
algebra is `Stacks.Descent.C1573.EqualizerLiftData.exists_eq_of_isNilpotent`.

## Main results

* `CommRingCat.C1573.surjective_and_ker_eq_map_of_isPushout`: in a pushout of a surjection, the
  opposite map is surjective with the extended kernel as kernel.
* `AlgebraicGeometry.C1573.exists_appTop_eq_of_isNilpotent_ker`: the lifting statement.

## References

* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace CommRingCat

open _root_.CommRingCat.C1573
/-- **The pushout of a surjection is the quotient by the extended kernel.** In a pushout square
of commutative rings `B' → B`, `B' → C'`, `B → C`, `C' → C` whose first map is surjective, the
map `C' → C` is surjective with kernel the extension of the kernel of `B' → B`. -/
theorem C1573.surjective_and_ker_eq_map_of_isPushout {B' B C' C : CommRingCat.{u}} {f : B' ⟶ B}
    {s : B' ⟶ C'} {g : B ⟶ C} {ρ : C' ⟶ C} (h : IsPushout f s g ρ)
    (hf : Function.Surjective f) :
    Function.Surjective ρ ∧ RingHom.ker ρ.hom = (RingHom.ker f.hom).map s.hom := by
  set J := (RingHom.ker f.hom).map s.hom
  have hle : J ≤ RingHom.ker ρ.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← CommRingCat.comp_apply, ← h.w, CommRingCat.comp_apply,
      RingHom.mem_ker.1 hx, map_zero]
  -- The comparison with the explicit quotient.
  let Q := CommRingCat.of (C' ⧸ J)
  let mk : C' ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let inl : B ⟶ Q := CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker f.hom)
      ((Ideal.Quotient.mk J).comp s.hom) (fun x hx ↦ Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_map_of_mem _ hx))).comp
    (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom)
  have hinl : f ≫ inl = s ≫ mk := by
    ext x
    simp only [inl, mk, CommRingCat.comp_apply, CommRingCat.hom_ofHom, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
  let φ : C ⟶ Q := h.desc inl mk hinl
  have hφ : ρ ≫ φ = mk := h.inr_desc _ _ _
  let ψ : Q ⟶ C := CommRingCat.ofHom (Ideal.Quotient.lift J ρ.hom fun x hx ↦ hle hx)
  have hψ : mk ≫ ψ = ρ := by ext x; rfl
  have hψφ : φ ≫ ψ = 𝟙 C := by
    refine h.hom_ext ?_ ?_
    · have : inl ≫ ψ = g := by
        ext x
        obtain ⟨x, rfl⟩ := hf x
        have h₁ := congr($(hinl) x)
        have h₂ := congr($(h.w) x)
        simp only [CommRingCat.comp_apply] at h₁ h₂
        rw [CommRingCat.comp_apply, h₁, h₂]
        rfl
      rw [← Category.assoc, h.inl_desc, this, Category.comp_id]
    · rw [← Category.assoc, hφ, hψ, Category.comp_id]
  refine ⟨fun c ↦ ?_, le_antisymm ?_ hle⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ c)
    refine ⟨x, ?_⟩
    have h₁ : ψ (φ c) = c := by rw [← CommRingCat.comp_apply, hψφ]; rfl
    rw [← hψ, CommRingCat.comp_apply]
    exact (congrArg ψ hx).trans h₁
  · intro x hx
    have : mk x = 0 := by
      rw [← hφ, CommRingCat.comp_apply, RingHom.mem_ker.1 hx, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this

end CommRingCat

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry.C1573
/-- **Lifting a regular function along a nilpotent thickening of an affine Čech nerve.** Consider
affine schemes and morphisms

* `j : W ⟶ W'` a closed immersion with nilpotent kernel on global sections;
* `a₀, a₁ : R' ⟶ W'` with `a₀` flat;
* `R = R' ×_{a₀, W', j} W`, with projections `r : R ⟶ R'` and `b₀ : R ⟶ W`, and a second map
  `b₁ : R ⟶ W` over `a₁`, such that `R = W ×_T W` along a flat surjection `π : W ⟶ T`;
* `R'' = R' ×_{a₁, W', a₀} R'` with projections `c₀₁, c₁₂` and a third map `c₀₂` with
  `c₀₂ a₀ = c₀₁ a₀`, `c₀₂ a₁ = c₁₂ a₁`;
* `R₂ = R'' ×_{c₀₁, R', r} R` with projections `r₂, e₀₁` and maps `e₀₂, e₁₂ : R₂ ⟶ R` over
  `c₀₂, c₁₂`, such that `R₂ = W ×_T R` along `e₁₂ b₁` and `e₀₁`.

Then for every regular function `x` on `T` there is a regular function `y` on `W'` with
`a₀^* y = a₁^* y` and `j^* y = π^* x`. -/
theorem C1573.exists_appTop_eq_of_isNilpotent_ker {T W' W R' R R'' R₂ : Scheme.{u}}
    [IsAffine T] [IsAffine W'] [IsAffine W] [IsAffine R'] [IsAffine R] [IsAffine R'']
    [IsAffine R₂]
    (j : W ⟶ W') [IsClosedImmersion j]
    (a₀ a₁ : R' ⟶ W') [Flat a₀]
    (r : R ⟶ R') (b₀ b₁ : R ⟶ W) (hR : IsPullback r b₀ a₀ j) (hb₁ : b₁ ≫ j = r ≫ a₁)
    (π : W ⟶ T) [Flat π] [Surjective π] (hRT : IsPullback b₀ b₁ π π)
    (c₀₁ c₀₂ c₁₂ : R'' ⟶ R') (hR'' : IsPullback c₀₁ c₁₂ a₁ a₀)
    (h₀₂₀ : c₀₂ ≫ a₀ = c₀₁ ≫ a₀) (h₀₂₁ : c₀₂ ≫ a₁ = c₁₂ ≫ a₁)
    (r₂ : R₂ ⟶ R'') (e₀₁ e₀₂ e₁₂ : R₂ ⟶ R) (hR₂ : IsPullback r₂ e₀₁ c₀₁ r)
    (he₀₂ : e₀₂ ≫ r = r₂ ≫ c₀₂) (he₁₂ : e₁₂ ≫ r = r₂ ≫ c₁₂)
    (hR₂T : IsPullback (e₁₂ ≫ b₁) e₀₁ π (b₀ ≫ π))
    (hJ : IsNilpotent (RingHom.ker j.appTop.hom)) (x : Γ(T, ⊤)) :
    ∃ y : Γ(W', ⊤), a₀.appTop y = a₁.appTop y ∧ j.appTop y = π.appTop x := by
  let : Algebra Γ(T, ⊤) Γ(W, ⊤) := π.appTop.hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ(R, ⊤) := (b₀ ≫ π).appTop.hom.toAlgebra
  let : Algebra Γ(R', ⊤) Γ(R'', ⊤) := c₀₁.appTop.hom.toAlgebra
  have : Module.FaithfullyFlat Γ(T, ⊤) Γ(W, ⊤) :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr <|
      RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
        ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).1
          ⟨inferInstance, inferInstance⟩)
  have hρ := CommRingCat.C1573.surjective_and_ker_eq_map_of_isPushout
    (isPushout_appTop_of_isPullback hR).flip
    (IsClosedImmersion.isAffine_surjective_of_isAffine j).2
  have hσ := CommRingCat.C1573.surjective_and_ker_eq_map_of_isPushout
    (isPushout_appTop_of_isPullback hR₂).flip hρ.1
  have hflat : Flat c₀₁ := MorphismProperty.of_isPullback hR''.flip inferInstance
  have hpush := isPushout_appTop_of_isPullback hR₂T
  have hw : π.appTop ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      Γ(W, ⊤) →+* Γ(W, ⊤) ⊗[Γ(T, ⊤)] Γ(R, ⊤)) = (b₀ ≫ π).appTop ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
          Γ(R, ⊤) →+* Γ(W, ⊤) ⊗[Γ(T, ⊤)] Γ(R, ⊤)) := by
    ext z
    show (algebraMap Γ(T, ⊤) Γ(W, ⊤) z) ⊗ₜ[Γ(T, ⊤)] (1 : Γ(R, ⊤)) =
      (1 : Γ(W, ⊤)) ⊗ₜ[Γ(T, ⊤)] (algebraMap Γ(T, ⊤) Γ(R, ⊤) z)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have key : ∀ {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ D) (g' : D ⟶ C),
      f ≫ g = f' ≫ g' → f.appTop.hom.comp g.appTop.hom = f'.appTop.hom.comp g'.appTop.hom := by
    intro A B C D f g f' g' h
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, h]
  let τ := hpush.desc _ _ hw
  let E : Stacks.Descent.C1573.EqualizerLiftData Γ(T, ⊤) Γ(W, ⊤) Γ(W', ⊤) Γ(R', ⊤) Γ(R'', ⊤)
      Γ(R, ⊤) Γ(R₂, ⊤) :=
    { π := j.appTop.hom
      surjective_π := (IsClosedImmersion.isAffine_surjective_of_isAffine j).2
      s := a₀.appTop.hom
      t := a₁.appTop.hom
      ρ := r.appTop.hom
      surjective_ρ := hρ.1
      ker_ρ := hρ.2
      sb := b₀.appTop.hom
      tb := b₁.appTop.hom
      ρ_comp_s := key _ _ _ _ hR.w
      ρ_comp_t := key _ _ _ _ hb₁.symm
      sb_comp_algebraMap := by
        show _ = (b₀ ≫ π).appTop.hom
        rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
        rfl
      tb_comp_algebraMap := by
        show _ = (b₀ ≫ π).appTop.hom
        rw [hRT.w, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
        rfl
      closure_range := CommRingCat.closure_range_union_range_eq_top_of_isPushout
        (isPushout_appTop_of_isPullback hRT)
      p₀₂ := c₀₂.appTop.hom
      p₁₂ := c₁₂.appTop.hom
      p₀₁_comp_s := key _ _ _ _ h₀₂₀.symm
      p₀₁_comp_t := key _ _ _ _ hR''.w
      p₀₂_comp_t := key _ _ _ _ h₀₂₁
      flat := (Scheme.Hom.flat_appTop c₀₁ :)
      σ := r₂.appTop.hom
      surjective_σ := hσ.1
      ker_σ := hσ.2
      q₀₁ := e₀₁.appTop.hom
      q₀₂ := e₀₂.appTop.hom
      q₁₂ := e₁₂.appTop.hom
      σ_comp_p₀₁ := key _ _ _ _ hR₂.w
      σ_comp_p₀₂ := key _ _ _ _ he₀₂.symm
      σ_comp_p₁₂ := key _ _ _ _ he₁₂.symm
      τ := τ.hom
      τ_comp_q₀₁ := by
        rw [← CommRingCat.hom_comp]
        exact congrArg CommRingCat.Hom.hom (hpush.inr_desc _ _ hw)
      τ_comp_e₂ := by
        rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
        exact congrArg CommRingCat.Hom.hom (hpush.inl_desc _ _ hw) }
  obtain ⟨y, hy, hy'⟩ := E.exists_eq_of_isNilpotent hJ x
  exact ⟨y, hy, hy'⟩

end AlgebraicGeometry

end
