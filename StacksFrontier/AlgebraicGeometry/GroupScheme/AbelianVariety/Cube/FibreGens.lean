module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.AtPoint

/-!
# The theorem of the cube: normalized generators of a trivial fibre

If the fibre `j_z^* N` is trivial, its generators can be rescaled by constants so that they
agree with the face generators along the two faces of the fibre, as required by
`Stacks.Cube.transfer_at`.

## Main results

* `Stacks.Cube.exists_const_smul_eq`: two generators of a trivial module on `A` differ by a
  unit constant of `k`.
* `Stacks.Cube.exists_normY`: the fibre has a generator satisfying `Stacks.Cube.NormY`.
* `Stacks.Cube.exists_normX`: the fibre has a generator satisfying `Stacks.Cube.NormX`.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

section General

variable {T Y₁ Y₂ Z : Scheme.{u}} (N : Z.Modules) (f₂ : T ⟶ Y₂) (b₂ : Y₂ ⟶ Z)

/-- The pullback `pulledGen₂` of `r • g` is the pullback of `r` times the pullback of `g`. -/
theorem pulledGen₂_smul (r : Γ(Y₂, ⊤)) (g : Γ((Scheme.Modules.pullback b₂).obj N, ⊤)) :
    pulledGen₂ N f₂ b₂ (g₂ := r • g) =
      f₂.appLE ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top _ _) r • pulledGen₂ N f₂ b₂ (g₂ := g) := by
  simp only [pulledGen₂]
  rw [pbS_smul, Scheme.Modules.Hom.app_smul]

/-- The pullback `pulledGen₁` of a generator is a generator. -/
theorem isGen_pulledGen₁ (f₁ : T ⟶ Y₁) (b₁ : Y₁ ⟶ Z) (hcomm : f₁ ≫ b₁ = f₂ ≫ b₂)
    {g₁ : Γ((Scheme.Modules.pullback b₁).obj N, ⊤)} (hg₁ : IsGen _ g₁) :
    IsGen _ (pulledGen₁ N f₁ b₁ f₂ b₂ hcomm (g₁ := g₁)) :=
  isGen_app_iso (isGen_app_iso (isGen_pbS f₁ hg₁) ((Scheme.Modules.pullbackComp f₁ b₁).app N))
    ((Scheme.Modules.pullbackCongr hcomm).app N)

end General

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
  (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) {V : A.left.Opens}
  (hzV : z ⁻¹ᵁ V = ⊤) (N : (P A).Modules)

/-- If the global sections of `A` are the constants `k`, then any two generators `γ₁`, `γ₂` of
a module `M` on `A` satisfy `γ₁ = c • γ₂` for a unit `c` of `k`. -/
theorem exists_const_smul_eq {M : A.left.Modules} {γ₁ γ₂ : Γ(M, ⊤)} (h₁ : IsGen M γ₁)
    (h₂ : IsGen M γ₂)
    (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop)) :
    ∃ c : k, IsUnit c ∧ γ₁ = (Stacks.Cech.baseRingHom A.hom ⊤).hom c • γ₂ := by
  obtain ⟨u, hu⟩ := exists_unit_smul_eq h₂ h₁
  obtain ⟨c, hc⟩ := hAc u
  have hc' : (Stacks.Cech.baseRingHom A.hom ⊤).hom c = u := by
    rw [← hc, Stacks.Cech.baseRingHom_eq_appLE A.hom ⊤ (Stacks.AffineProduct.le_preimage_top _ _)]
    change (A.hom.appLE ⊤ ⊤ _) ((Scheme.ΓSpecIso (.of k)).inv c) =
      A.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv c)
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨c, ?_, by rw [hc']; exact hu⟩
  by_contra hcu
  have hc0 : c = 0 := by
    by_contra h
    exact hcu (isUnit_iff_ne_zero.mpr h)
  rw [hc0, map_zero] at hc'
  have := u.isUnit
  rw [← hc'] at this
  have hnt : Nontrivial Γ(A.left, ⊤) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (eA (A := A)).appTop.hom h
    rw [map_zero, map_one] at h'
    exact zero_ne_one ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.injective
      (by simp at h'))
  exact not_isUnit_zero this

variable {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)
  {σ₀ : Γ(fibreModule z hzk hzV N, ⊤)} (hσ₀ : IsGen _ σ₀)
  (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop))

include hg₁ hσ₀ hAc in
/-- The fibre module has a generator `σY` satisfying the normalization `NormY` along the face
`e × A` with respect to `g₁`. -/
theorem exists_normY : ∃ σY : Γ(fibreModule z hzk hzV N, ⊤),
    IsGen _ σY ∧ NormY z hzk hzV N (g₁ := g₁) (σY := σY) := by
  have h₁ := isGen_pulledGen₁ N (faceYB A) (jzV z hzk hzV ≫ (PV V).ι) (τz z hzk) (face₁ A)
    (hcommY z hzk hzV) hg₁
  have h₂ := isGen_pulledGen₂ N (faceYB A) (jzV z hzk hzV ≫ (PV V).ι)
    (isGen_app_iso hσ₀ (restrictPullbackIso (jzV z hzk hzV) (PV V).ι N))
  obtain ⟨c, hcu, hc⟩ := exists_const_smul_eq h₁ h₂ hAc
  refine ⟨(Stacks.Cech.baseRingHom (A ⊗ A).hom ⊤).hom c • σ₀,
    isGen_unit_smul hσ₀ (hcu.map (Stacks.Cech.baseRingHom (A ⊗ A).hom ⊤).hom).unit, ?_⟩
  refine hc.trans ?_
  rw [Scheme.Modules.Hom.app_smul, pulledGen₂_smul]
  congr 1
  exact (appLE_algebraMap (A ⊗ A).hom A.hom (faceYB A) faceYB_hom _ c).symm

include hg₂ hσ₀ hAc in
/-- The fibre module has a generator `σX` satisfying the normalization `NormX` along the face
`A × e` with respect to `g₂`. -/
theorem exists_normX : ∃ σX : Γ(fibreModule z hzk hzV N, ⊤),
    IsGen _ σX ∧ NormX z hzk hzV N (g₂ := g₂) (σX := σX) := by
  have h₁ := isGen_pulledGen₁ N (faceXB A) (jzV z hzk hzV ≫ (PV V).ι) (τz z hzk) (face₂ A)
    (hcommX z hzk hzV) hg₂
  have h₂ := isGen_pulledGen₂ N (faceXB A) (jzV z hzk hzV ≫ (PV V).ι)
    (isGen_app_iso hσ₀ (restrictPullbackIso (jzV z hzk hzV) (PV V).ι N))
  obtain ⟨c, hcu, hc⟩ := exists_const_smul_eq h₁ h₂ hAc
  refine ⟨(Stacks.Cech.baseRingHom (A ⊗ A).hom ⊤).hom c • σ₀,
    isGen_unit_smul hσ₀ (hcu.map (Stacks.Cech.baseRingHom (A ⊗ A).hom ⊤).hom).unit, ?_⟩
  refine hc.trans ?_
  rw [Scheme.Modules.Hom.app_smul, pulledGen₂_smul]
  congr 1
  exact (appLE_algebraMap (A ⊗ A).hom A.hom (faceXB A) faceXB_hom _ c).symm

end Stacks.Cube

end
