module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.ChartUnique

/-!
# The theorem of the cube: propagation of trivial fibres

Let `N` be an invertible module on `(A × A) × A` with trivial pullbacks to the two faces over the
third factor. If the fibre of `N` over a rational point `z'` of an affine chart `V` is trivial,
then the fibre over every other rational point `z` of `V` has a nonzero global section
(`Stacks.Cube.false_of_fibre`): a section of `N` over `V` lifting the face generators near `z'`
would otherwise vanish by cohomology and base change at `z`.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator Stacks.FlatComplexNakayama

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

attribute [local instance] faceModule

/-- The fibre over a chart is the intrinsic fibre. -/
noncomputable def fibreIso (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) {V : A.left.Opens}
    (hzV : z ⁻¹ᵁ V = ⊤) (N : (P A).Modules) :
    fibreModule z hzk hzV N ≅ (Scheme.Modules.pullback (jz z hzk)).obj N :=
  restrictPullbackIso _ _ N ≪≫ (Scheme.Modules.pullbackCongr (jzV_ι z hzk hzV)).app N

/-- The fibre over the identity is the third face. -/
theorem jz_eA : jz (eA (A := A)) eA_hom = (Stacks.Groupoids.cubeFace₃ A).left := by
  have h1 := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₃_cubeProj₁ A)
  have h2 := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₃_cubeProj₂ A)
  have h3 := congrArg CommaMorphism.left (Stacks.Groupoids.cubeFace₃_cubeProj₃ A)
  simp only [Stacks.Groupoids.cubeProj₁, Stacks.Groupoids.cubeProj₂, Stacks.Groupoids.cubeProj₃,
    CategoryTheory.Hom.one_def, Over.comp_left, Over.fst_left, Over.snd_left, Over.toUnit_left,
    Over.tensorObj_hom] at h1 h2 h3
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · exact (jz_q_assoc _ eA_hom (bx A)).trans h1.symm
  · exact (jz_q_assoc _ eA_hom (bz A)).trans h2.symm
  · exact (jz_r _ eA_hom).trans h3.symm

variable {N : (P A).Modules}
  {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)

include hg₁ in
/-- **Normalizing the second face generator.** -/
theorem exists_normalized {g : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg : IsGen _ g)
    (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop)) :
    ∃ g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤), IsGen _ g₂ ∧
      Normalized N (g₁ := g₁) (g₂ := g₂) := by
  have h₁ := isGen_pulledGen₁ N σe (face₂ A) σe (face₁ A) σe_face₁ hg₁
  have h₂ := isGen_pulledGen₂ N σe (face₂ A) hg
  obtain ⟨c, hcu, hc⟩ := exists_const_smul_eq h₁ h₂ hAc
  refine ⟨(Stacks.Cech.baseRingHom (A ⊗ A).hom ⊤).hom c • g,
    isGen_unit_smul hg (hcu.map (Stacks.Cech.baseRingHom (A ⊗ A).hom ⊤).hom).unit, ?_⟩
  refine hc.trans ?_
  rw [pulledGen₂_smul]
  congr 1
  have hs : σe (A := A) ≫ (A ⊗ A).hom = A.hom := by
    change σe ≫ bx A ≫ A.hom = A.hom
    rw [σe_bx_assoc, show eA (A := A) ≫ A.hom = 𝟙 _ from eA_hom, Category.comp_id]
  exact (appLE_algebraMap (A ⊗ A).hom A.hom σe hs _ c).symm

variable {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)
  {V : A.left.Opens} (hV : IsAffineOpen V) {ι : Type u} [Finite ι]
  (U : ι → A.left.Opens) {a₀ : ι} (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)

variable [IsAlgClosed k] [LocallyOfFiniteType A.hom] [Smooth A.hom]

omit [IsAlgClosed k] [LocallyOfFiniteType A.hom] in
include hg₁ hg₂ ha₀ in
/-- **A trivial fibre forbids a fibre without sections in the same chart.** -/
theorem false_of_fibre (h : ChartHyp hV U N)
    (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
    (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop))
    (hBc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ (A ⊗ A).hom.appTop))
    (hnorm : Normalized N (g₁ := g₁) (g₂ := g₂)) [IsDomain (chartRing V)]
    (z' : Spec (.of k) ⟶ A.left) (hzk' : z' ≫ A.hom = 𝟙 _) (hzV' : z' ⁻¹ᵁ V = ⊤)
    {σ₀ : Γ(fibreModule z' hzk' hzV' N, ⊤)} (hσ₀ : IsGen _ σ₀)
    (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) (hzV : z ⁻¹ᵁ V = ⊤)
    (h0 : ∀ s : Γ(fibreModule z hzk hzV N, ⊤), s = 0) : False := by
  obtain ⟨a, ha, y, hy0, hy⟩ := exists_lift_at ha₀ hg₁ hg₂ hU hUcov hAc hBc h hnorm z' hzk' hzV' hσ₀
  have hker := ker_d₀_eq_bot_of_fibre hUcov h z hzk hzV h0
  have hy00 : y = 0 := by
    have : y ∈ LinearMap.ker (d₀ hV U N) := hy0
    rw [hker] at this
    exact this
  rw [hy00, map_zero] at hy
  have h1 := congrFun (congrArg Prod.fst hy) (fun _ => a₀)
  let := cochainModule U A.hom 0
  change (0 : Γ(B A, faceOpen V U (fun _ => a₀))) = faceAct V U _ a * faceψ V U 0 (one U) _ at h1
  rw [faceψ_one, mul_one] at h1
  have h2 := congrArg (σe.appLE _ V (le_σe_preimage V U ha₀)) h1
  rw [map_zero] at h2
  simp only [faceAct] at h2
  change (0 : chartRing V) = σe.appLE _ V _ ((bz A).appLE V _ _ a) at h2
  rw [appLE_comp, appLE_congr (σe_bz (A := A)), id_appLE_self] at h2
  exact ha (by rw [← h2, map_zero])

end Stacks.Cube

end
