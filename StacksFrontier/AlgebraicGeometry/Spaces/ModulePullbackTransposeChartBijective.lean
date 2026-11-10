module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso

/-!
# The transpose of a map into a direct image, on a chart diagram over a surjection of rings

Let `i : Z ⟶ X` be a morphism of algebraic spaces, `M` a quasi-coherent `𝒪_X`-module, `F` an
`𝒪_Z`-module and `ψ : M ⟶ i_* F`, with transpose `ψ♭ : i^* M ⟶ F`. On a diagram `d` of affine
étale charts `U ⟶ V` over `i` such that

* `𝒪_X(V) → 𝒪_Z(U)` is surjective and kills an ideal `J`,
* the chart projection `(i_* F)(V) ⟶ F(U)` is bijective,
* `ψ` is surjective on the sections over `V` with kernel inside `J • M(V)`,

the component of `ψ♭` over `U` is bijective: `(i^* M)(U) = 𝒪_Z(U) ⊗_{𝒪_X(V)} M(V)`
(`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`) is
`M(V) / J M(V)` there, and `ψ♭` sends `1 ⊗ m` to the projection of `ψ(m)`. In the proof of
[Stacks, Tag 0CX9] this is how `Fₙ = F ⊗ 𝒪_{Xₙ}` is read off `H⁰(K) ⊗_A Aₙ ≅ Γ(U, iₙ,* Fₙ)` on an
affine chart.

## Main results

* `AlgebraicGeometry.Space.bijective_homEquiv_symm_val_app_of_surjective`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Z : AlgebraicSpaces B S hS}

/-- The transpose `ψ♭ : i^* M ⟶ F` of `ψ : M ⟶ i_* F` sends the chart section of `s` to the
chart projection of `ψ(s)`. -/
theorem homEquiv_symm_val_app_modulePullbackChartSection (i : Z ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (F : Modules.{u, u} B S hS Z.1 Z.2)
    (ψ : M ⟶ (modulePushforward B S hS i).obj F) (d : ChartDiagram B S hS Z.1 X.1 i.hom)
    (s : M.val.obj (op d.V)) :
    ((((modulePullbackAdjunction B S hS i).homEquiv M F).symm ψ).val.app (op d.U))
        (modulePullbackChartSection B S hS i M d s) =
      modulePushforwardCounitApp B S hS i F d (ψ.val.app (op d.V) s) := by
  rw [← modulePullbackUnitSection_eq_modulePullbackChartSection,
    ← modulePullbackHomFMap_app]
  change modulePushforwardCounitApp B S hS i F d
    ((((modulePullbackAdjunction B S hS i).homEquiv M F)
      (((modulePullbackAdjunction B S hS i).homEquiv M F).symm ψ)).val.app (op d.V) s) = _
  rw [Equiv.apply_symm_apply]

/-- **Bijectivity of the transpose on a chart diagram over a surjection of rings.** -/
theorem bijective_homEquiv_symm_val_app_of_surjective (i : Z ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (F : Modules.{u, u} B S hS Z.1 Z.2) (ψ : M ⟶ (modulePushforward B S hS i).obj F)
    (d : ChartDiagram B S hS Z.1 X.1 i.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS Z.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (hκ : Function.Bijective (modulePushforwardCounitApp B S hS i F d))
    (hρ : Function.Surjective (chartDiagramRestrict B S hS i d))
    (J : Ideal (chartRing B S hS X.1 X.2 d.V))
    (hJ : J ≤ RingHom.ker (chartDiagramRestrict B S hS i d))
    (hψs : Function.Surjective (ψ.val.app (op d.V)))
    (hψk : ∀ m, ψ.val.app (op d.V) m = 0 →
      m ∈ J • (⊤ : Submodule (chartRing B S hS X.1 X.2 d.V) (M.val.obj (op d.V)))) :
    Function.Bijective
      ((((modulePullbackAdjunction B S hS i).homEquiv M F).symm ψ).val.app (op d.U)) := by
  let := chartDiagramAlgebra B S hS i d
  let u := ((modulePullbackAdjunction B S hS i).homEquiv M F).symm ψ
  have hθ := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS i M hM d
    haU haV
  -- every element of `𝒪_Z(U) ⊗ M(V)` is some `1 ⊗ m`
  have hone : ∀ z : TensorProduct (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Z.1 Z.2 d.U)
      (M.val.obj (op d.V)),
      ∃ m, z = TensorProduct.tmul _ (1 : chartRing B S hS Z.1 Z.2 d.U) m := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a s =>
      obtain ⟨r, rfl⟩ := hρ a
      refine ⟨r • s, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1
      exact (Algebra.algebraMap_eq_smul_one r).trans rfl
    | add x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨m', rfl⟩ := hy
      exact ⟨m + m', (TensorProduct.tmul_add _ _ _).symm⟩
  have hval : ∀ m, u.val.app (op d.U) (modulePullbackChartBaseChange B S hS i M d
      (TensorProduct.tmul _ (1 : chartRing B S hS Z.1 Z.2 d.U) m)) =
        modulePushforwardCounitApp B S hS i F d (ψ.val.app (op d.V) m) := by
    intro m
    rw [modulePullbackChartBaseChange_tmul, one_smul]
    exact homEquiv_symm_val_app_modulePullbackChartSection i M F ψ d m
  have hzero : ∀ m ∈ J • (⊤ : Submodule (chartRing B S hS X.1 X.2 d.V) (M.val.obj (op d.V))),
      TensorProduct.tmul (chartRing B S hS X.1 X.2 d.V)
        (1 : chartRing B S hS Z.1 Z.2 d.U) m = 0 := by
    intro m hm
    refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => ?_)
    · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      change TensorProduct.tmul _ (chartDiagramRestrict B S hS i d a) n = 0
      rw [RingHom.mem_ker.1 (hJ ha), TensorProduct.zero_tmul]
    · rw [TensorProduct.tmul_add, hx, hy, add_zero]
  have hcomp : Function.Bijective
      (u.val.app (op d.U) ∘ modulePullbackChartBaseChange B S hS i M d) := by
    refine ⟨fun z z' hzz' => ?_, fun y => ?_⟩
    · obtain ⟨m, rfl⟩ := hone z
      obtain ⟨m', rfl⟩ := hone z'
      have h2 : ψ.val.app (op d.V) (m - m') = 0 := by
        rw [map_sub, hκ.1 ((hval m).symm.trans (hzz'.trans (hval m'))), sub_self]
      have h3 := hzero _ (hψk _ h2)
      rwa [TensorProduct.tmul_sub, sub_eq_zero] at h3
    · obtain ⟨x, rfl⟩ := hκ.2 y
      obtain ⟨m, rfl⟩ := hψs x
      exact ⟨_, hval m⟩
  exact (Function.Bijective.of_comp_iff _ hθ).1 hcomp

end AlgebraicGeometry.Space

end
